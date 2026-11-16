# 05: Choose the first contract workloads

Type: grilling

Status: resolved

## Question

Which end-to-end contract workloads should the first compiler release support? Name one or two concrete examples and identify the circuit behavior each requires, such as private inputs, public inputs, ledger state, constraints, and outputs.

## Answer

Use a private one-time claim as Nightlean's first end-to-end workload. The circuit takes a private eligibility value, checks membership against a public commitment or root, derives a nullifier, and uses ledger state to reject reuse. This exercises private and public inputs, hashing, constraints, and state transitions without making the project financial-only.
