use constraint_framework::expr::{Expr, Constant};
use constraint_framework::{Component, ComponentBuilder};
use serde::Deserialize;
use anyhow::{Result, bail};
use std::{env, fs};
use std::path::Path;

#[derive(Debug, Deserialize)]
#[serde(tag = "type")]
enum ZKExpr {
    #[serde(rename = "lit")]
    Literal { val: String },

    #[serde(rename = "witness")]
    WitnessVar { id: usize },

    #[serde(rename = "add")]
    Add { a: Box<ZKExpr>, b: Box<ZKExpr> },

    #[serde(rename = "sub")]
    Sub { a: Box<ZKExpr>, b: Box<ZKExpr> },

    #[serde(rename = "neg")]
    Neg { a: Box<ZKExpr> },

    #[serde(rename = "mul")]
    Mul { a: Box<ZKExpr>, b: Box<ZKExpr> },

    #[serde(rename = "eq")]
    Eq { a: Box<ZKExpr>, b: Box<ZKExpr> },

    #[serde(rename = "lookup")]
    Lookup,
}

#[derive(Debug, Deserialize)]
struct CircuitIR {
    expr: ZKExpr,
    constraints: Vec<ZKExpr>,
}

fn convert_expr(expr: &ZKExpr) -> Expr {
    match expr {
        ZKExpr::Literal { val } => {
            let parsed: f64 = val.parse().expect("invalid number");
            Expr::Constant(Constant::from(parsed))
        }
        ZKExpr::WitnessVar { id } => Expr::Cell(*id as u64),
        ZKExpr::Add { a, b } => Expr::Add(Box::new(convert_expr(a)), Box::new(convert_expr(b))),
        ZKExpr::Sub { a, b } => Expr::Sub(Box::new(convert_expr(a)), Box::new(convert_expr(b))),
        ZKExpr::Neg { a } => Expr::Neg(Box::new(convert_expr(a))),
        ZKExpr::Mul { a, b } => Expr::Mul(Box::new(convert_expr(a)), Box::new(convert_expr(b))),
        ZKExpr::Eq { .. } => panic!("Eq is not an expression"),
        ZKExpr::Lookup => todo!("lookup handling not implemented"),
    }
}

fn build_constraints(constraints: &[ZKExpr]) -> Component {
    let mut builder = ComponentBuilder::default();

    for (i, constraint) in constraints.iter().enumerate() {
        match constraint {
            ZKExpr::Eq { a, b } => {
                let lhs = convert_expr(a);
                let rhs = convert_expr(b);
                builder.assert_equal(lhs, rhs);
            }
            _ => panic!("Unsupported top-level constraint: {:?}", constraint),
        }
    }

    builder.build("lean_program")
}


fn main() -> Result<()> {
    let json_path = Path::new("ZkLeanCompiler/Frontend/out.json");
    if !json_path.exists() {
        bail!("Missing circuit output: {:?}", json_path);
    }

    let json = fs::read_to_string(json_path)?;
    let circuit: CircuitIR = serde_json::from_str(&json)?;
    println!("✅ Parsed circuit: {} constraints", circuit.constraints.len());

    let component = build_constraints(&circuit.constraints);
    println!("✅ Built constraint component with {} rows", component.num_rows());

    // Future: add prover + witness assignment

    Ok(())
}



