#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""
B站话题浏览量查询工具
====================

支持两种查询方式：
  1. 按关键词搜索话题  ->  python bili_topic.py search 原神
  2. 按话题 ID 查详情  ->  python bili_topic.py detail 61457

数据来源（B站 Web 端公开接口，无需登录）：
  搜索: https://api.bilibili.com/x/topic/pub/search
  详情: https://api.bilibili.com/x/topic/web/details/top
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
import os
import random
import re
import sys
import time
import unicodedata
import urllib.parse
from typing import Any, Dict, Iterable, List, Optional

import requests

UA = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36"
)
API_SEARCH = "https://api.bilibili.com/x/topic/pub/search"
API_DETAIL = "https://api.bilibili.com/x/topic/web/details/top"
API_VIDEO = "https://api.bilibili.com/x/web-interface/view"
API_VIDEO_TAGS = "https://api.bilibili.com/x/tag/archive/tags"
API_TAG_INFO = "https://api.bilibili.com/x/tag/info"
API_VIDEO_SEARCH = "https://api.bilibili.com/x/web-interface/search/type"
API_WBI_SEARCH = "https://api.bilibili.com/x/web-interface/wbi/search/type"
API_NAV = "https://api.bilibili.com/x/web-interface/nav"
API_FINGER = "https://api.bilibili.com/x/frontend/finger/spi"

# WBI 签名用的密钥重排表
WBI_TABLE = [
    46, 47, 18, 2, 53, 8, 23, 32, 15, 50, 10, 31, 58, 3, 45, 28, 1, 59, 62, 42,
    22, 27, 56, 12, 40, 61, 24, 5, 55, 36, 63, 21, 33, 16, 14, 49, 38, 39, 51,
    57, 29, 44, 6, 34, 11, 37, 43, 25, 9, 60, 20, 48, 30, 41, 7, 17, 54, 13,
    19, 35, 52, 4, 26,
]
HISTORY_FILE = "tag_history.json"   # 标签播放量快照，用于生成日/月变化曲线
# 播放量统计口径版本：口径变更时旧快照会被自动忽略，避免增幅失真
METRIC_VERSION = 2
TIMEOUT = 15
RETRY = 4
MIN_INTERVAL = 0.6              # 两次请求之间的最小间隔（秒）
RISK_STATUS = {412}             # HTTP 层面的风控状态码
RISK_CODES = {-352, -412, -1200}  # B站业务层面的风控返回码


# -----------------------------------------------------------------------------#
# 基础工具
# -----------------------------------------------------------------------------#
def to_int(v: Any) -> int:
    """把接口返回的播放量/时间戳等字段安全转成 int。"""
    try:
        return int(v or 0)
    except (TypeError, ValueError):
        return 0


def disp_width(s: str) -> int:
    """计算字符串在终端中的显示宽度（中文按 2 个字符算）。"""
    return sum(2 if unicodedata.east_asian_width(ch) in "WF" else 1 for ch in s)


def pad(s: str, width: int) -> str:
    """按显示宽度右补空格。"""
    return s + " " * max(0, width - disp_width(s))


def fmt_num(n: Optional[int]) -> str:
    """把大数字格式化成 万/亿 形式，便于阅读。"""
    if n is None:
        return "-"
    if n >= 100_000_000:
        return f"{n / 100_000_000:.2f}亿"
    if n >= 10_000:
        return f"{n / 10_000:.1f}万"
    return str(n)


def ts_to_str(ts: int) -> str:
    return time.strftime("%Y-%m-%d", time.localtime(ts)) if ts else "-"


# -----------------------------------------------------------------------------#
# Zipf 幂律拟合：用头部榜单外推全部视频播放量
# -----------------------------------------------------------------------------#
def fit_zipf(plays: List[int]) -> Optional[tuple]:
    """对 (rank, play) 做 log-log 最小二乘拟合，返回 (alpha, C)，play ≈ C / rank^alpha。"""
    xs, ys = [], []
    for i, p in enumerate(sorted(plays, reverse=True), 1):
        if p and p > 0:
            xs.append(math.log(i))
            ys.append(math.log(p))
    n = len(xs)
    if n < 5:
        return None
    mx, my = sum(xs) / n, sum(ys) / n
    den = sum((x - mx) ** 2 for x in xs)
    if den <= 0:
        return None
    slope = sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / den
    # 约束在常见 UGC 幂律区间，避免样本异常导致外推失真
    alpha = min(max(-slope, 0.8), 2.0)
    return alpha, math.exp(my - slope * mx)


def zipf_tail(alpha: float, c: float, start: int, end: int) -> int:
    """Σ_{k=start..end} C·k^(-alpha)，逐项求和到 2 万，其余用积分近似。"""
    start, end = max(1, start), max(1, end)
    if end < start:
        return 0
    k = min(end, 20_000)
    s = sum(c * (i ** -alpha) for i in range(start, k + 1)) if k >= start else 0
    if end > k:
        if abs(alpha - 1) < 1e-6:
            s += c * (math.log(end) - math.log(k))
        else:
            s += c * (end ** (1 - alpha) - k ** (1 - alpha)) / (1 - alpha)
    return int(s)


# -----------------------------------------------------------------------------#
# 请求封装
# -----------------------------------------------------------------------------#
class BiliTopicClient:
    def __init__(self) -> None:
        self.session = requests.Session()
        self.session.headers.update(
            {
                "User-Agent": UA,
                "Referer": "https://www.bilibili.com/v/topic/detail",
                "Origin": "https://www.bilibili.com",
                "Accept": "application/json, text/plain, */*",
                "Accept-Language": "zh-CN,zh;q=0.9",
            }
        )
        self._last_call = 0.0
        self._mixin: Optional[str] = None
        self._bootstrap()

    def _bootstrap(self) -> None:
        """访问首页拿 buvid3 等匿名 Cookie，否则接口会被风控拦截。"""
        try:
            self.session.get("https://www.bilibili.com/", timeout=TIMEOUT)
        except requests.RequestException:
            pass
        # 用 finger/spi 重新签发 buvid3 / buvid4，风控后尤其需要
        try:
            r = self.session.get(API_FINGER, timeout=TIMEOUT)
            d = ((r.json() or {}).get("data") or {})
            for name, key in (("buvid3", "b_3"), ("buvid4", "b_4")):
                if d.get(key):
                    self.session.cookies.set(name, d[key], domain=".bilibili.com")
        except Exception:  # noqa: BLE001
            pass

    def _refresh(self) -> None:
        """被风控（412 / -352）后重建匿名 Cookie。"""
        self.session.cookies.clear()
        self._mixin = None
        self._bootstrap()

    def _throttle(self) -> None:
        """限制请求频率，降低触发风控的概率。"""
        wait = MIN_INTERVAL - (time.time() - self._last_call)
        if wait > 0:
            time.sleep(wait + random.uniform(0, 0.25))
        self._last_call = time.time()

    def _get(self, url: str, params: Dict[str, Any]) -> Dict[str, Any]:
        last_err: Optional[Exception] = None
        for i in range(RETRY):
            self._throttle()
            try:
                r = self.session.get(url, params=params, timeout=TIMEOUT)
                if r.status_code in RISK_STATUS:      # 412 风控
                    last_err = RuntimeError(f"{r.status_code} 触发风控，已刷新 Cookie 重试")
                    self._refresh()
                    time.sleep(1.5 * (i + 1))
                    continue
                r.raise_for_status()
                data = r.json()
                code = data.get("code")
                if code != 0:
                    if code in RISK_CODES:            # -352 / -412 风控
                        last_err = RuntimeError(f"code={code} {data.get('message')}（风控）")
                        self._refresh()
                        time.sleep(1.5 * (i + 1))
                        continue
                    raise RuntimeError(
                        f"接口返回错误 code={code} "
                        f"message={data.get('message')}"
                    )
                return data.get("data") or {}
            except Exception as e:  # noqa: BLE001
                last_err = e
                time.sleep(0.8 * (i + 1) + random.uniform(0, 0.3))
        raise RuntimeError(f"请求失败：{last_err}")

    # ---- 关键词搜索话题 -------------------------------------------------- #
    def search(self, keyword: str, limit: int = 20) -> List[Dict[str, Any]]:
        items: List[Dict[str, Any]] = []
        offset = 0
        page_size = 20
        while len(items) < limit:
            data = self._get(
                API_SEARCH,
                {"keywords": keyword, "page_size": page_size, "offset": offset},
            )
            batch = data.get("topic_items") or []
            if not batch:
                break
            items.extend(batch)
            page = data.get("page_info") or {}
            if not page.get("has_more"):
                break
            new_offset = page.get("offset")
            if not new_offset or new_offset <= offset:
                break
            offset = new_offset
            time.sleep(0.3)
        return items[:limit]

    # ---- 按 ID 查话题详情 ------------------------------------------------- #
    def detail(self, topic_id: int) -> Dict[str, Any]:
        data = self._get(API_DETAIL, {"topic_id": topic_id, "source": "Web"})
        top = data.get("top_details") or {}
        item = top.get("topic_item") or {}
        if not item:
            raise RuntimeError(f"话题 {topic_id} 不存在或已下线")
        item = dict(item)
        item["creator"] = (top.get("topic_creator") or {}).get("name", "-")
        item["creator_uid"] = (top.get("topic_creator") or {}).get("uid")
        return item

    # ---- 视频信息与标签统计 ------------------------------------------------ #
    def video_info(self, video: str) -> Dict[str, Any]:
        """获取视频标题/UP主/播放等基础数据。video 可为 BV号/av号/链接。"""
        vid = parse_video_id(video)
        params = {"bvid": vid} if vid.upper().startswith("BV") else {"aid": vid}
        self.session.headers["Referer"] = f"https://www.bilibili.com/video/{vid}/"
        try:
            return self._get(API_VIDEO, params)
        finally:
            self.session.headers["Referer"] = "https://www.bilibili.com/v/topic/detail"

    # ---- 视频搜索（用于统计标签播放量） ----------------------------------- #
    def _mixin_key(self) -> str:
        """取 WBI 签名密钥（nav 未登录也返回 wbi_img，故不走 _get）。"""
        if self._mixin:
            return self._mixin
        self._throttle()
        r = self.session.get(API_NAV, timeout=TIMEOUT)
        w = ((r.json() or {}).get("data") or {}).get("wbi_img") or {}
        raw = (
            w["img_url"].rsplit("/", 1)[1].split(".")[0]
            + w["sub_url"].rsplit("/", 1)[1].split(".")[0]
        )
        self._mixin = "".join(raw[i] for i in WBI_TABLE)[:32]
        return self._mixin

    def _wbi(self, params: Dict[str, Any]) -> Dict[str, Any]:
        p = dict(params)
        p["wts"] = int(time.time())
        q = urllib.parse.urlencode(sorted(p.items()))
        p["w_rid"] = hashlib.md5((q + self._mixin_key()).encode()).hexdigest()
        return p

    def _search_once(self, keyword: str, page: int, order: str,
                     wbi: bool, pubtime: Optional[tuple] = None) -> List[Dict[str, Any]]:
        base: Dict[str, Any] = {"search_type": "video", "keyword": keyword,
                                "order": order, "page": page}
        if pubtime:
            base["pubtime_begin_s"], base["pubtime_end_s"] = pubtime
        if wbi:
            params: Dict[str, Any] = self._wbi(base)
            url = API_WBI_SEARCH
        else:
            params = base
            url = API_VIDEO_SEARCH
        data = self._get(url, params)
        out = []
        for v in (data or {}).get("result") or []:
            title = re.sub(r"<[^>]+>", "", v.get("title") or "").strip()
            play = to_int(v.get("play"))
            pubdate = to_int(v.get("pubdate"))
            out.append({"bvid": v.get("bvid"), "title": title, "play": play,
                        "pubdate": pubdate, "author": v.get("author")})
        return out

    def search_videos(self, keyword: str, page: int = 1,
                      order: str = "click",
                      pubtime: Optional[tuple] = None) -> List[Dict[str, Any]]:
        """按关键词搜索视频（用于采样标签播放量）。

        搜索接口最容易触发 412 风控：失败后刷新匿名 Cookie 并递增退避重试，
        全部失败再尝试 WBI 接口；仍无结果才报错。
        """
        last: Optional[Exception] = None
        for attempt in range(3):
            try:
                return self._search_once(keyword, page, order, wbi=False, pubtime=pubtime)
            except Exception as e:  # noqa: BLE001
                last = e
                self._refresh()
                time.sleep(2.0 * (attempt + 1) + random.uniform(0, 1))

        try:                                   # 最后尝试 WBI 签名接口
            r = self._search_once(keyword, page, order, wbi=True, pubtime=pubtime)
            if r:
                return r
        except Exception:  # noqa: BLE001
            pass

        raise RuntimeError(
            f"视频搜索接口暂时不可用（多为风控 412，请稍后再试或减少采样页数）：{last}"
        )

    def tag_weekly_new(self, tag: str, pages: int = 2,
                       weeks: int = 48) -> Dict[str, Any]:
        """统计该标签最近 weeks 周内，每一周【新发布】视频的播放量变化。

        做法：对每一周单独用「发布时间区间」筛选（pubtime_begin_s /
        pubtime_end_s）并按播放量排序采样，各周样本量一致，可直接横向比较。
        """
        base = self.tag_info(tag)
        now = int(time.time())
        week = 7 * 86400

        buckets = []
        for i in range(weeks):
            start = now - (weeks - i) * week
            end = min(start + week, now)
            seen: Dict[str, Dict[str, Any]] = {}
            for p in range(1, max(1, min(pages, 50)) + 1):
                batch = self.search_videos(
                    base["name"], page=p, order="click",
                    pubtime=(start, end),
                )
                if not batch:
                    break
                for v in batch:
                    if v["bvid"]:
                        seen.setdefault(v["bvid"], v)

            hit = list(seen.values())
            view = sum(v["play"] for v in hit)
            buckets.append({
                "label": f"第{i + 1}周",
                "range": f"{time.strftime('%m-%d', time.localtime(start))}"
                           f"~{time.strftime('%m-%d', time.localtime(end))}",
                "start": start,
                "end": end,
                "count": len(hit),
                "view": view,
                "view_text": fmt_num(view),
                "avg": int(view / len(hit)) if hit else 0,
                "avg_text": fmt_num(int(view / len(hit))) if hit else "-",
                "capped": len(seen) >= pages * 20,
            })

        sample_total = sum(b["count"] for b in buckets)
        truncated = any(b.get("capped") for b in buckets)
        earliest = buckets[0]["start"] if buckets else now
        covered_days = max(0, int((now - earliest) / 86400))

        return {
            "tag": base,
            "weeks": buckets,
            "sample_total": sample_total,
            "truncated": truncated,
            "covered_days": covered_days,
            "covered_from_text": ts_to_str(earliest),
            "covered_to_text": ts_to_str(now),
        }
    def tag_view_sample(self, tag_name: str, pages: int = 5,
                        total_use: Optional[int] = None) -> Dict[str, Any]:
        """按播放量排序分页抓取榜单，用 Zipf 幂律拟合外推该标签下全部视频的播放量。"""
        seen: Dict[str, Dict[str, Any]] = {}
        done = 0
        for p in range(1, max(1, min(pages, 50)) + 1):
            batch = self.search_videos(tag_name, page=p, order="click")
            if not batch:
                break
            for v in batch:
                if v["bvid"]:
                    seen.setdefault(v["bvid"], v)
            done += 1
            time.sleep(0.25)

        vids = sorted(seen.values(), key=lambda v: v["play"], reverse=True)
        sample_sum = sum(v["play"] for v in vids)
        sample = len(vids)

        # 头部用实测值，未抓到的长尾用 Zipf 模型外推：play ≈ C / rank^alpha
        fit = fit_zipf([v["play"] for v in vids])
        est, alpha, tail = sample_sum, None, 0
        if fit and total_use and total_use > sample:
            alpha, c = fit
            tail = zipf_tail(alpha, c, sample + 1, total_use)
            est = sample_sum + tail

        return {
            "view_total": est,          # 全量估算 = 实测头部 + 模型长尾
            "sample_view_sum": sample_sum,   # 实测部分（下界）
            "tail_view": tail,          # 长尾部分（由模型估计）
            "sample": sample,
            "pages": done,
            "alpha": alpha,
            "estimated": bool(fit and total_use and total_use > sample),
        }

    def tag_info(self, tag: str) -> Dict[str, Any]:
        """按 tag_id 或标签名查询标签基础信息。"""
        t = (tag or "").strip()
        if not t:
            raise ValueError("请输入标签名或 tag_id")
        params = {"tag_id": int(t)} if t.isdigit() else {"tag_name": t}
        info = self._get(API_TAG_INFO, params)
        if not info.get("tag_id"):
            raise RuntimeError(f"未找到标签：{t}")
        c = info.get("count") or {}
        return {
            "tag_id": info.get("tag_id"),
            "name": (info.get("tag_name") or t).strip(),
            "use": c.get("use"),
        }

    def tag_report(self, tag: str, pages: int = 5) -> Dict[str, Any]:
        """单个标签的完整报告：基础信息 + 全量播放量估算。

        采样被风控时不再整体失败，而是返回基础信息并附带 warning。
        """
        base = self.tag_info(tag)
        warning = None
        try:
            s = self.tag_view_sample(base["name"], pages, total_use=base.get("use"))
            if not s["sample"]:
                warning = "未抓到任何样本视频，可能触发了接口风控，请稍后重试或减少页数。"
            base.update({
                "view_total": s["view_total"],
                "sample_view_sum": s["sample_view_sum"],
                "tail_view": s["tail_view"],
                "sample": s["sample"],
                "alpha": s["alpha"],
                "estimated": s["estimated"],
            })
        except Exception as e:  # noqa: BLE001
            warning = str(e)
            base.update({
                "view_total": None, "sample_view_sum": 0, "tail_view": 0,
                "sample": 0, "alpha": None, "estimated": False,
            })
        return {"tag": base, "warning": warning}

    def video_tag_stats(self, video: str, limit: int = 20,
                        with_view: bool = True, pages: int = 3) -> List[Dict[str, Any]]:
        """获取视频的标签，以及每个标签的全量播放量估算，按播放量降序。"""
        tags = self._get(API_VIDEO_TAGS, {"bvid": parse_video_id(video)}) or []
        out: List[Dict[str, Any]] = []
        for t in tags[:limit]:
            info = self._get(API_TAG_INFO, {"tag_id": t["tag_id"]}) or {}
            c = info.get("count") or {}
            row = {
                "tag_id": t.get("tag_id"),
                "name": (t.get("tag_name") or "").strip(),
                "use": c.get("use"),
                "view_total": None,
                "sample_view_sum": 0,
                "tail_view": 0,
                "sample": 0,
                "alpha": None,
                "estimated": False,
            }
            if with_view and row["name"]:
                try:
                    s = self.tag_view_sample(row["name"], pages, total_use=row["use"])
                    row["view_total"] = s["view_total"]
                    row["sample_view_sum"] = s["sample_view_sum"]
                    row["tail_view"] = s["tail_view"]
                    row["sample"] = s["sample"]
                    row["alpha"] = s["alpha"]
                    row["estimated"] = s["estimated"]
                except Exception:  # noqa: BLE001 采样失败不影响其他指标
                    pass
            out.append(row)
            time.sleep(0.25)
        out.sort(key=lambda x: x.get("view_total") or x.get("use") or 0, reverse=True)
        return out


# -----------------------------------------------------------------------------#
# 标签播放量快照（用于日/月变化曲线）
# -----------------------------------------------------------------------------#
def history_path() -> str:
    return os.path.join(os.path.dirname(os.path.abspath(__file__)), HISTORY_FILE)


def load_history(tag_id: Optional[int] = None) -> List[Dict[str, Any]]:
    p = history_path()
    if not os.path.exists(p):
        return []
    try:
        with open(p, encoding="utf-8") as f:
            recs = json.load(f)
    except Exception:  # noqa: BLE001
        return []
    # 只保留当前统计口径的快照，避免口径变更导致增幅失真
    recs = [r for r in recs if r.get("v") == METRIC_VERSION]
    if tag_id is not None:
        recs = [r for r in recs if r.get("tag_id") == tag_id]
    return sorted(recs, key=lambda r: r.get("ts") or 0)


def save_snapshot(tags: List[Dict[str, Any]]) -> None:
    """把本次查询到的标签播放量写入快照文件（保留一年）。"""
    usable = [t for t in tags if t.get("view_total") is not None]
    if not usable:
        return
    now = int(time.time())
    recs = load_history()
    for t in usable:
        recs.append({
            "tag_id": t["tag_id"],
            "name": t["name"],
            "view": t["view_total"],
            "ts": now,
            "v": METRIC_VERSION,
        })
    recs = [r for r in recs if (r.get("ts") or 0) > now - 365 * 86400]
    try:
        with open(history_path(), "w", encoding="utf-8") as f:
            json.dump(recs, f, ensure_ascii=False)
    except OSError:
        pass


def aggregate_history(recs: List[Dict[str, Any]], mode: str = "day") -> List[Dict[str, Any]]:
    """把快照按日/月聚合，输出 [{label, view, delta}]。"""
    groups: Dict[str, int] = {}
    for r in recs:
        if not r.get("ts"):
            continue
        t = time.localtime(r["ts"])
        key = time.strftime("%m-%d", t) if mode == "day" else time.strftime("%Y-%m", t)
        groups[key] = r.get("view") or 0   # 同一周期取最后一次快照

    # 同一天内多次查询时，按时间点展开，保证当天也能画出趋势
    if mode == "day" and len(groups) == 1 and len(recs) >= 2:
        pairs = [(time.strftime("%H:%M", time.localtime(r["ts"])), r.get("view") or 0)
                 for r in recs if r.get("ts")]
    else:
        pairs = sorted(groups.items())

    out, prev = [], None
    for k, v in pairs:
        out.append({"label": k, "view": v,
                    "delta": None if prev is None else v - prev})
        prev = v
    return out


def parse_video_id(text: str) -> str:
    """从 BV号 / av号 / 完整链接中提取视频 ID。"""
    text = (text or "").strip()
    m = re.search(r"(BV[0-9A-Za-z]{10})", text, re.I)
    if m:
        return m.group(1)
    m = re.search(r"av(\d+)", text, re.I)
    if m:
        return m.group(1)
    if text.isdigit():
        return text
    raise ValueError(f"无法识别的视频号：{text}")


def normalize(rows: Iterable[Dict[str, Any]]) -> List[Dict[str, Any]]:
    """统一搜索/详情两种来源的数据结构。"""
    out = []
    for r in rows:
        out.append(
            {
                "id": r.get("id"),
                "name": r.get("name", "").strip(),
                "view": r.get("view"),
                "discuss": r.get("discuss"),
                "fav": r.get("fav"),
                "dynamics": r.get("dynamics"),
                "desc": (r.get("description") or "").replace("\n", " ").strip(),
                "creator": r.get("creator", "-"),
                "like": r.get("like"),
                "share": r.get("share"),
                "ctime": r.get("ctime"),
                "url": r.get("jump_url") or r.get("share_url"),
            }
        )
    return out


# 浏览量分布区间（左闭右开，最后一个区间无上限）
VIEW_BUCKETS = [
    ("< 1万", 0, 10_000),
    ("1万 - 10万", 10_000, 100_000),
    ("10万 - 100万", 100_000, 1_000_000),
    ("100万 - 1000万", 1_000_000, 10_000_000),
    ("1000万 - 1亿", 10_000_000, 100_000_000),
    ("≥ 1亿", 100_000_000, None),
]


def summarize(rows: List[Dict[str, Any]]) -> Dict[str, Any]:
    """对一批话题做聚合统计：总量/均值/中位数/极值/TOP5 占比/分布区间。"""
    if not rows:
        return {"count": 0}

    views = sorted(r.get("view") or 0 for r in rows)
    discusses = [r.get("discuss") or 0 for r in rows]
    n = len(views)
    total = sum(views)

    def median(xs: List[int]) -> float:
        m = len(xs) // 2
        return xs[m] if len(xs) % 2 else (xs[m - 1] + xs[m]) / 2

    buckets = []
    for label, lo, hi in VIEW_BUCKETS:
        hit = [v for v in views if v >= lo and (hi is None or v < hi)]
        buckets.append({"label": label, "count": len(hit), "view_total": sum(hit)})

    top5 = sum(views[-5:]) if n >= 5 else total
    top_row = max(rows, key=lambda r: r.get("view") or 0)

    return {
        "count": n,
        "view_total": total,
        "view_avg": total / n,
        "view_median": median(views),
        "view_max": views[-1],
        "view_max_name": top_row.get("name", "-"),
        "view_min": views[0],
        "discuss_total": sum(discusses),
        "top5_share": (top5 / total) if total else 0.0,
        "buckets": buckets,
    }


def print_stats(st: Dict[str, Any], keyword: str = "") -> None:
    if not st.get("count"):
        print("没有可统计的数据。")
        return
    title = f"关键词「{keyword}」" if keyword else "本次查询"
    print(f"{title}共 {st['count']} 个话题的统计：\n")
    print(f"  浏览量合计   : {fmt_num(st['view_total'])}（{st['view_total']}）")
    print(f"  浏览量均值   : {fmt_num(int(st['view_avg']))}")
    print(f"  浏览量中位数 : {fmt_num(int(st['view_median']))}")
    print(f"  最高 / 最低  : {fmt_num(st['view_max'])}（{st['view_max_name']}） / {fmt_num(st['view_min'])}")
    print(f"  讨论数合计   : {fmt_num(st['discuss_total'])}")
    print(f"  TOP5 占比    : {st['top5_share'] * 100:.1f}%\n")
    print("  浏览量分布：")
    maxc = max(b["count"] for b in st["buckets"]) or 1
    for b in st["buckets"]:
        bar = "█" * int(round(b["count"] / maxc * 24))
        print(f"    {pad(b['label'], 14)} {bar:<24} {b['count']} 个"
              f"（{fmt_num(b['view_total'])}）")


# -----------------------------------------------------------------------------#
# 输出
# -----------------------------------------------------------------------------#
def print_table(rows: List[Dict[str, Any]]) -> None:
    if not rows:
        print("未查询到任何话题。")
        return

    headers = ["话题ID", "话题名称", "浏览量", "原始浏览数", "讨论数"]
    max_name = min(30, max(disp_width(r["name"]) for r in rows))
    widths = [10, max(max_name, 8), 12, 14, 12]

    # 搜索结果不含创建者信息，全部为空时隐藏该列
    has_creator = any(r.get("creator") and r["creator"] != "-" for r in rows)
    if has_creator:
        max_creator = min(14, max(disp_width(r["creator"] or "-") for r in rows))
        headers.append("创建者")
        widths.append(max(max_creator, 8))
    print("  ".join(pad(h, w) for h, w in zip(headers, widths)))
    print("-" * (sum(widths) + 2 * (len(widths) - 1)))

    def cut(s: str, w: int) -> str:
        s = s or "-"
        if disp_width(s) <= w:
            return s
        res, cur = "", 0
        for ch in s:
            c = 2 if unicodedata.east_asian_width(ch) in "WF" else 1
            if cur + c > w - 1:
                break
            res += ch
            cur += c
        return res + "…"

    for r in rows:
        cells = [
            str(r["id"] or "-"),
            cut(r["name"], widths[1]),
            fmt_num(r["view"]),
            str(r["view"] if r["view"] is not None else "-"),
            fmt_num(r["discuss"]),
        ]
        if has_creator:
            cells.append(cut(r["creator"], widths[5]))
        print("  ".join(pad(c, w) for c, w in zip(cells, widths)))


def print_detail(item: Dict[str, Any]) -> None:
    print(f"话题名称  : {item.get('name', '-')}")
    print(f"话题 ID   : {item.get('id', '-')}")
    print(
        f"浏览量    : {fmt_num(item.get('view'))}"
        f"（{item.get('view', 0)}）"
    )
    print(f"讨论数    : {fmt_num(item.get('discuss'))}（{item.get('discuss', 0)}）")
    print(f"动态数    : {fmt_num(item.get('dynamics'))}")
    print(f"收藏数    : {fmt_num(item.get('fav'))}")
    print(f"点赞/分享 : {fmt_num(item.get('like'))} / {fmt_num(item.get('share'))}")
    print(f"创建者    : {item.get('creator', '-')}（uid={item.get('creator_uid')}）")
    print(f"创建时间  : {ts_to_str(item.get('ctime', 0))}")
    desc = (item.get("description") or "").replace("\n", " ").strip()
    if desc:
        print(f"简介      : {desc}")
    print(f"话题链接  : {item.get('jump_url') or item.get('share_url') or '-'}")


def print_vtag(video: Dict[str, Any], tags: List[Dict[str, Any]]) -> None:
    stat = video.get("stat") or {}
    print(f"视频标题  : {video.get('title', '-')}")
    print(f"UP主      : {(video.get('owner') or {}).get('name', '-')}（{(video.get('bvid')) or '-'}）")
    print(f"播放/弹幕 : {fmt_num(stat.get('view'))} / {fmt_num(stat.get('danmaku'))}")
    print(f"点赞/投币 : {fmt_num(stat.get('like'))} / {fmt_num(stat.get('coin'))}")
    print(f"收藏/分享 : {fmt_num(stat.get('favorite'))} / {fmt_num(stat.get('share'))}")
    print(f"评论数    : {fmt_num(stat.get('reply'))}")
    print(f"\n标签统计（共 {len(tags)} 个，按播放量排序）：\n")

    headers = ["标签", "全量播放量", "头部样本", "样本合计", "使用视频数", "tag_id"]
    widths = [
        max(8, min(22, max(disp_width(t["name"]) for t in tags))),
        14, 10, 12, 12, 12,
    ]
    print("  ".join(pad(h, w) for h, w in zip(headers, widths)))
    print("-" * (sum(widths) + 2 * (len(widths) - 1)))
    for t in tags:
        cells = [
            cut_text(t["name"], widths[0]),
            fmt_num(t["view_total"]) if t["view_total"] is not None else "-",
            f"{t['sample']} 个" if t["sample"] else "-",
            fmt_num(t["sample_view_sum"]) if t["sample_view_sum"] else "-",
            fmt_num(t["use"]),
            str(t["tag_id"]),
        ]
        print("  ".join(pad(c, w) for c, w in zip(cells, widths)))
    print("\n  注：全量播放量由头部榜单按 Zipf 幂律外推到该标签下全部视频，覆盖长尾；")
    print("      头部样本为搜索接口按播放量排序分页抓到的部分（每页 20 个）。")
    print("      可用 -p/--pages 增大页数提高精度；B站已停用标签自身的 view 字段。")


def sparkline(views: List[int]) -> str:
    blocks = "▁▂▃▄▅▆▇█"
    lo, hi = min(views), max(views)
    return "".join(
        blocks[0 if hi == lo else int((v - lo) / (hi - lo) * (len(blocks) - 1))]
        for v in views
    )


def print_series(series: List[Dict[str, Any]], title: str) -> None:
    if len(series) < 2:
        print(f"  {title}：快照不足（{len(series)} 个点），再查一次即可生成曲线。")
        return
    views = [s["view"] for s in series]
    first, last = series[0]["view"], series[-1]["view"]
    delta = last - first
    pct = (delta / first * 100) if first else 0.0
    print(f"  {title}：{sparkline(views)}  {fmt_num(first)} → {fmt_num(last)}"
          f"（{'+' if delta >= 0 else '-'}{fmt_num(abs(delta))}，"
          f"{'+' if pct >= 0 else '-'}{abs(pct):.2f}%）"
          f"  [{series[0]['label']} → {series[-1]['label']}]")


def print_weekly(rep: Dict[str, Any]) -> None:
    weeks = rep.get("weeks") or []
    t = rep.get("tag") or {}
    print(f"标签名称  : {t.get('name', '-')}（tag_id={t.get('tag_id')}）")
    print(f"区间      : 最近 {len(weeks)} 周（{len(weeks) * 7} 天），抓到 {rep.get('sample_total', 0)} 个新发布视频")
    if rep.get("truncated"):
        print("  注意：请求页数已达上限，样本可能被截断，统计为区间内的一部分。")
    print()
    headers = ["周次", "日期区间", "新发布视频", "播放量合计", "平均播放"]
    widths = [8, 20, 12, 14, 12]
    print("  ".join(pad(h, w) for h, w in zip(headers, widths)))
    print("-" * (sum(widths) + 2 * (len(widths) - 1)))
    for b in weeks:
        cells = [b["label"], b["range"], f"{b['count']} 个",
                 b["view_text"], b["avg_text"]]
        print("  ".join(pad(c, w) for c, w in zip(cells, widths)))


def print_tag_report(rep: Dict[str, Any]) -> None:
    t = rep["tag"]
    print(f"标签名称  : {t['name']}（tag_id={t['tag_id']}）")
    if rep.get("warning"):
        print(f"\n[提示] {rep['warning']}\n")
    alpha = f"，α={t['alpha']:.2f}" if t.get("alpha") else ""
    if t.get("view_total") is None:
        print("全量播放量: 暂不可用（采样失败）")
    else:
        print(f"全量播放量: {fmt_num(t['view_total'])}（{t['view_total']}）  [估算]")
        print(f"  ├ 实测头部: {t['sample']} 个视频，合计 {fmt_num(t['sample_view_sum'])}（确定值）")
        print(f"  └ 长尾外推: 剩余 {fmt_num((t['use'] or 0) - t['sample'])} 个视频，"
              f"约 {fmt_num(t['tail_view'])}（Zipf 幂律{alpha}）")
    print(f"使用视频数: {fmt_num(t['use'])}")
    print("\n提示：本工具不再展示日/月曲线，请改用 `weekly` 命令查看近 48 周新发布视频播放量变化。")


def print_tag_trend(tags: List[Dict[str, Any]]) -> None:
    """打印基于本地快照的日/月播放量变化曲线（ASCII）。"""
    for mode, title in (("day", "日"), ("month", "月")):
        printed = False
        for t in tags:
            series = aggregate_history(load_history(t["tag_id"]), mode)
            if len(series) < 2:
                continue
            if not printed:
                print(f"\n{title}播放量变化曲线（本地快照，查询越多曲线越完整）：")
                printed = True
            views = [s["view"] for s in series]
            lo, hi = min(views), max(views)
            blocks = "▁▂▃▄▅▆▇█"
            spark = "".join(
                blocks[0 if hi == lo else int((v - lo) / (hi - lo) * (len(blocks) - 1))]
                for v in views
            )
            delta = series[-1]["view"] - series[0]["view"]
            print(f"  {cut_text(t['name'], 14):<16}{spark}  "
                  f"{fmt_num(series[0]['view'])} → {fmt_num(series[-1]['view'])}"
                  f"（{'+' if delta >= 0 else '-'}{fmt_num(abs(delta))}）")
        if not printed and mode == "day":
            print("\n提示：本地暂无足够历史快照，多查询几次后即可生成日/月变化曲线。")


def cut_text(s: str, w: int) -> str:
    """按显示宽度截断（print_table 内部逻辑的简化版）。"""
    # 去掉 emoji 等非 BMP 字符，避免 Windows GBK 控制台输出报错
    s = "".join(ch for ch in (s or "") if ord(ch) <= 0xFFFF) or "-"
    if disp_width(s) <= w:
        return s
    res, cur = "", 0
    for ch in s:
        cw = 2 if unicodedata.east_asian_width(ch) in "WF" else 1
        if cur + cw > w - 1:
            return res + "…"
        res += ch
        cur += cw
    return res


def dump_tags(tags: List[Dict[str, Any]], as_json: bool, csv_path: Optional[str]) -> None:
    if as_json:
        print(json.dumps(tags, ensure_ascii=False, indent=2))
    if csv_path:
        with open(csv_path, "w", encoding="utf-8-sig", newline="") as f:
            w = csv.DictWriter(f, fieldnames=["tag_id", "name", "view_total",
                                              "sample_view_sum", "use"])
            w.writeheader()
            w.writerows(tags)
        print(f"\n已导出 CSV: {csv_path}")


def dump(rows: List[Dict[str, Any]], raw: List[Dict[str, Any]],
         as_json: bool, csv_path: Optional[str]) -> None:
    if as_json:
        print(json.dumps(raw, ensure_ascii=False, indent=2))
    if csv_path:
        with open(csv_path, "w", encoding="utf-8-sig", newline="") as f:
            w = csv.DictWriter(
                f, fieldnames=["id", "name", "view", "discuss", "fav", "dynamics", "creator", "desc"]
            )
            w.writeheader()
            w.writerows(rows)
        print(f"\n已导出 CSV: {csv_path}")


# -----------------------------------------------------------------------------#
# CLI
# -----------------------------------------------------------------------------#
def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="bili_topic.py",
        description="B站话题浏览量查询（关键词搜索 / 话题ID 精确查询）",
        formatter_class=argparse.RawTextHelpFormatter,
    )
    sub = p.add_subparsers(dest="cmd", required=True)

    s = sub.add_parser("search", help="按关键词搜索话题")
    s.add_argument("keyword", help="搜索关键词，例如 原神")
    s.add_argument("-n", "--limit", type=int, default=20, help="返回条数，默认 20")
    s.add_argument(
        "--sort",
        choices=["view", "discuss", "default"],
        default="default",
        help="排序方式：view=浏览量 / discuss=讨论数 / default=接口默认，默认 default",
    )

    st = sub.add_parser("stats", help="对关键词搜索结果做聚合统计")
    st.add_argument("keyword", help="搜索关键词，例如 原神")
    st.add_argument("-n", "--limit", type=int, default=30, help="统计样本条数，默认 30")

    tg = sub.add_parser("tag", help="查询单个标签的全量播放量估算")
    tg.add_argument("name", help="标签名或 tag_id，例如 千早爱音 / 37656829")
    tg.add_argument("-p", "--pages", type=int, default=5,
                    help="采样页数，默认 5（每页 20 个视频，越大越准越慢）")
    tg.add_argument("--json", action="store_true", help="额外输出原始 JSON")

    wk = sub.add_parser("weekly", help="某标签最近 48 周每周新发布视频的播放量变化")
    wk.add_argument("name", help="标签名或 tag_id，例如 咕咕嘎嘎 / 3138035")
    wk.add_argument("-p", "--pages", type=int, default=2,
                    help="每周抓取页数，默认 2（每页 20 个，即每周约 40 个样本）")
    wk.add_argument("-w", "--weeks", type=int, default=48, help="统计周数，默认 48")
    wk.add_argument("--json", action="store_true", help="额外输出原始 JSON")

    vt = sub.add_parser("vtag", help="统计视频标签（每个标签的全量播放量）")
    vt.add_argument("video", help="视频 BV号 / av号 / 链接，例如 BV1Yunh6FECN")
    vt.add_argument("-n", "--limit", type=int, default=20, help="统计标签数，默认 20")
    vt.add_argument("-p", "--pages", type=int, default=3, help="每标签采样页数，默认 3")

    d = sub.add_parser("detail", help="按话题 ID 精确查询（可传多个）")
    d.add_argument("topic_id", nargs="+", type=int, help="话题 ID，例如 61457")

    for sp in (s, st, vt, d):
        sp.add_argument("--json", action="store_true", help="额外输出接口原始 JSON")
        sp.add_argument("--csv", metavar="PATH", help="导出为 CSV 文件")

    return p


def main(argv: Optional[List[str]] = None) -> int:
    args = build_parser().parse_args(argv)
    client = BiliTopicClient()

    try:
        if args.cmd == "search":
            raw = client.search(args.keyword, args.limit)
            if args.sort == "view":
                raw.sort(key=lambda x: x.get("view") or 0, reverse=True)
            elif args.sort == "discuss":
                raw.sort(key=lambda x: x.get("discuss") or 0, reverse=True)
            rows = normalize(raw)
            print(f"关键词「{args.keyword}」共获取 {len(rows)} 个话题：\n")
            if rows:
                top = max(rows, key=lambda r: r["view"] or 0)
                print_table(rows)
                print(
                    f"\n浏览量最高：{top['name']} —— {fmt_num(top['view'])}"
                    f"（{top['view']} 次浏览，ID={top['id']}）"
                )
            else:
                print("未查询到任何话题。")
            dump(rows, raw, args.json, args.csv)

        elif args.cmd == "stats":
            raw = client.search(args.keyword, args.limit)
            rows = normalize(raw)
            if not rows:
                print("未查询到任何话题。")
                return 0
            print_stats(summarize(rows), args.keyword)
            dump(rows, raw, args.json, args.csv)

        elif args.cmd == "tag":
            rep = client.tag_report(args.name, args.pages)
            print_tag_report(rep)
            if args.json:
                print(json.dumps(rep, ensure_ascii=False, indent=2))

        elif args.cmd == "weekly":
            rep = client.tag_weekly_new(args.name, args.pages, args.weeks)
            print_weekly(rep)
            print()
            print("播放量变化（按周）：")
            print_series(rep["weeks"], "周")
            if args.json:
                print(json.dumps(rep, ensure_ascii=False, indent=2))

        elif args.cmd == "vtag":
            info = client.video_info(args.video)
            tags = client.video_tag_stats(args.video, args.limit, pages=args.pages)
            if not tags:
                print("该视频没有标签。")
                return 0
            save_snapshot(tags)
            print_vtag(info, tags)
            print_tag_trend(tags)
            dump_tags(tags, args.json, args.csv)

        else:  # detail
            raw, rows = [], []
            for tid in args.topic_id:
                try:
                    item = client.detail(tid)
                    raw.append(item)
                    rows.append(normalize([item])[0])
                except Exception as e:  # noqa: BLE001
                    print(f"[跳过] {tid}: {e}", file=sys.stderr)
                time.sleep(0.3)
            print()
            for i, item in enumerate(raw):
                if i:
                    print("-" * 46)
                print_detail(item)
            if len(raw) > 1:
                print("\n汇总：\n")
                print_table(rows)
            dump(rows, raw, args.json, args.csv)

    except Exception as e:  # noqa: BLE001
        print(f"错误：{e}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
