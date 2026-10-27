# -*- coding: utf-8 -*-
"""
B站视频标签统计 —— Web 界面
============================

启动：  python web_app.py
访问：  http://127.0.0.1:5173

功能：
  1. 输入视频 BV号 → 列出该视频全部标签及各自总播放量
  2. 输入标签名 / tag_id → 查询该标签总播放量，以及近 48 周新发布视频播放量变化

数据层复用 bili_topic.py 中的 BiliTopicClient。
"""

from __future__ import annotations

import threading

from flask import Flask, jsonify, render_template, request

from bili_topic import (
    BiliTopicClient,
    fmt_num,
)

app = Flask(__name__)

# 可重入锁：接口处理函数外层持锁后，get_client() 内部还会再次获取同一把锁，
# 若使用普通 Lock 会造成同线程死锁，请求永久挂起。
_api_lock = threading.RLock()
_client: BiliTopicClient | None = None

def get_client() -> BiliTopicClient:
    global _client
    with _api_lock:
        if _client is None:
            _client = BiliTopicClient()
        return _client


def pack_tag(t: dict) -> dict:
    """单个标签 → 前端展示结构。"""
    d = dict(t)
    d["use_text"] = fmt_num(t.get("use"))
    d["view_text"] = fmt_num(t.get("view_total")) if t.get("view_total") is not None else "-"
    d["sample_text"] = fmt_num(t.get("sample_view_sum"))
    d["tail_text"] = fmt_num(t.get("tail_view"))
    d["alpha_text"] = f"{t['alpha']:.2f}" if t.get("alpha") else "-"
    return d


@app.after_request
def add_cors(resp):
    """允许从其他地址（如 IDE 预览页、本地文件）打开的前端直连本机后端。"""
    resp.headers["Access-Control-Allow-Origin"] = "*"
    return resp


@app.route("/")
def index():
    return render_template("index.html")


@app.get("/api/vtag")
def api_vtag():
    """视频 → 标签列表 + 每个标签的总播放量估算。"""
    video = (request.args.get("video") or "").strip()
    if not video:
        return jsonify({"ok": False, "message": "请输入视频 BV号 / av号 / 链接"}), 400

    try:
        pages = int(request.args.get("pages", 3))
    except ValueError:
        pages = 3
    pages = max(1, min(25, pages))

    try:
        with _api_lock:
            cli = get_client()
            info = cli.video_info(video)
            tags = cli.video_tag_stats(video, 20, with_view=True, pages=pages)
    except Exception as e:  # noqa: BLE001
        return jsonify({"ok": False, "message": str(e)}), 502

    if not tags:
        return jsonify({"ok": False, "message": "该视频没有标签"}), 404

    stat = info.get("stat") or {}
    return jsonify(
        {
            "ok": True,
            "video": {
                "title": info.get("title"),
                "owner": (info.get("owner") or {}).get("name"),
                "bvid": info.get("bvid"),
                "view_text": fmt_num(stat.get("view")),
                "like_text": fmt_num(stat.get("like")),
                "coin_text": fmt_num(stat.get("coin")),
                "favorite_text": fmt_num(stat.get("favorite")),
                "danmaku_text": fmt_num(stat.get("danmaku")),
                "reply_text": fmt_num(stat.get("reply")),
                "share_text": fmt_num(stat.get("share")),
            },
            "tags": [pack_tag(t) for t in tags],
        }
    )


@app.get("/api/tag")
def api_tag():
    """单个标签（名称或 tag_id）→ 总播放量估算。"""
    q = (request.args.get("q") or "").strip()
    if not q:
        return jsonify({"ok": False, "message": "请输入标签名或 tag_id"}), 400

    try:
        pages = int(request.args.get("pages", 5))
    except ValueError:
        pages = 5
    pages = max(1, min(50, pages))

    try:
        with _api_lock:
            rep = get_client().tag_report(q, pages)
    except Exception as e:  # noqa: BLE001
        return jsonify({"ok": False, "message": str(e)}), 502

    tag = rep["tag"]
    return jsonify(
        {
            "ok": True,
            "warning": rep.get("warning"),
            "tag": {
                "tag_id": tag["tag_id"],
                "name": tag["name"],
                "view_total": tag["view_total"],
                "view_text": fmt_num(tag["view_total"]) if tag["view_total"] is not None else "-",
                "sample": tag["sample"],
                "sample_text": fmt_num(tag.get("sample_view_sum") or 0),
                "tail_text": fmt_num(tag.get("tail_view") or 0),
                "alpha_text": f"{tag['alpha']:.2f}" if tag.get("alpha") else "-",
                "use_text": fmt_num(tag.get("use")),
            },
        }
    )


@app.get("/api/tag/weekly")
def api_tag_weekly():
    """某标签最近若干周，每周新发布视频的播放量变化。"""
    q = (request.args.get("q") or "").strip()
    if not q:
        return jsonify({"ok": False, "message": "请输入标签名或 tag_id"}), 400

    try:
        pages = int(request.args.get("pages", 2))
    except ValueError:
        pages = 2
    pages = max(1, min(10, pages))

    try:
        weeks = int(request.args.get("weeks", 48))
    except ValueError:
        weeks = 48
    weeks = max(1, min(52, weeks))

    try:
        with _api_lock:
            rep = get_client().tag_weekly_new(q, pages, weeks)
    except Exception as e:  # noqa: BLE001
        return jsonify({"ok": False, "message": str(e)}), 502

    return jsonify({
        "ok": True,
        "tag": rep["tag"],
        "weeks": rep["weeks"],
        "sample_total": rep["sample_total"],
        "truncated": rep["truncated"],
        "covered_days": rep["covered_days"],
        "covered_from_text": rep["covered_from_text"],
        "covered_to_text": rep["covered_to_text"],
    })


if __name__ == "__main__":
    app.run(host="127.0.0.1", port=5173, debug=False, threaded=True)
