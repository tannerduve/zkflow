# Running the demo

From the repo root:

1) Build the demo executable:

`lake build zkflow_demo`

2) Run the compiler on a `.zk` file (prints AST + circuit):

`lake exe zkflow_demo examples/mix_all.zk`

3) Print only the parsed AST:

`lake exe zkflow_demo examples/mix_all.zk --ast`

4) Print only the compiled circuit:

`lake exe zkflow_demo examples/mix_all.zk --circuit`

5) Add your own program:

- Create `examples/my_prog.zk`
- Run `lake exe zkflow_demo examples/my_prog.zk`
