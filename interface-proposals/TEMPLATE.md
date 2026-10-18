---
issue_id: Module-YYYYMMDD-short-name
title: 精确的问题标题
summary: 简述问题、当前建议与尚未完成的边界。
responsibility_module: Main
targets:
  - KIP126.Main.example
baseline_commit: 待记录实际提交
reporter_agent: 待记录独立报告员
independent_of_discoverer_and_implementer: true
evidence_level: 尚未完成独立核验；不得填作已形式化反例
status: draft
human_decision: null
---

# 接口审查报告

## 请求人类决定的具体问题

明确是否已有具体可审阅的修改方案；当前无需决定时如实说明。既有授权不重复请求。

## 原接口、背景与问题成因

记录实际完整签名、宇宙、实例、固定对象、全部前提和原结论；附源码位置与接口锁。

## 真实前提与对象核对

逐项核对问题发生在同一个实际对象上。区分抽象模型反例、固定数学对象反例与 Lean 反例。

## 独立证据与复现

记录实际执行的检查、输入指纹、复现方法与结果；列明直接及传递待补依赖。小型证据可放同目录 evidence/，用相对链接引用。

## 方案及精确差异

写出每个候选的完整原/新陈述，说明是否已证明；不能以排除已知反例冒充正确性证明。

## 下游影响

列出受影响调用方、责任归属、锁与测试需要怎样更新。

## 阻塞范围与继续项

只标记确实受影响目标；区分可继续补证、等待具体授权与未提出完整方案的研究。

## 人类审核记录

尚未批准。只有收到明确人类决定后，才更新 human_decision 与 status，保留范围、日期和未批准部分。
