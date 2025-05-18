import json
from pathlib import Path
from graphviz import Digraph

def format_expr(expr, ctx):
    typ = expr["type"]

    if typ == "lit":
        val = expr["val"]
        label = f"lit:{val}"
        ctx["graph"].node(label, label, shape="circle", style="filled", fillcolor="lightgray")
        return label

    if typ == "witness":
        wid = expr["id"]
        label = f"w{wid}"
        ctx["graph"].node(label, label, shape="doublecircle", style="filled", fillcolor="lightblue")
        ctx["witnesses"].add(label)
        return label

    if typ in {"add", "sub", "mul", "eq"}:
        a = format_expr(expr["a"], ctx)
        b = format_expr(expr["b"], ctx)
        gid = f"{typ}_{ctx['counter']}"
        ctx["counter"] += 1
        ctx["graph"].node(gid, typ, shape="box", style="filled", fillcolor="lightyellow")
        ctx["graph"].edge(a, gid)
        ctx["graph"].edge(b, gid)
        return gid

    if typ == "neg":
        a = format_expr(expr["a"], ctx)
        gid = f"neg_{ctx['counter']}"
        ctx["counter"] += 1
        ctx["graph"].node(gid, "neg", shape="box", style="filled", fillcolor="lightyellow")
        ctx["graph"].edge(a, gid)
        return gid

    if typ == "lookup":
        gid = f"lookup_{ctx['counter']}"
        ctx["counter"] += 1
        ctx["graph"].node(gid, "lookup", shape="box", style="filled", fillcolor="pink")
        return gid

    return "?"

def build_graph(data):
    dot = Digraph(format="png")
    ctx = {"graph": dot, "counter": 0, "witnesses": set()}

    output = format_expr(data["expr"], ctx)
    dot.node("output", "output", shape="octagon", style="filled", fillcolor="lightgreen")
    dot.edge(output, "output")

    for i, constraint in enumerate(data["constraints"]):
        lhs = format_expr(constraint["a"], ctx)
        rhs = format_expr(constraint["b"], ctx)
        cmp = f"assert_{i}"
        dot.node(cmp, f"==", shape="diamond", style="filled", fillcolor="orange")
        dot.edge(lhs, cmp)
        dot.edge(rhs, cmp)
    return dot

def main():
    path = Path("ZkLeanCompiler/Frontend/out.json")
    if not path.exists():
        print("Circuit JSON not found.")
        return

    data = json.loads(path.read_text())
    g = build_graph(data)

    out_file = "circuit_graph"
    g.render(out_file, view=True)
    print(f"Graph saved to {out_file}.png")

if __name__ == "__main__":
    main()
