use clippy_utils::ty::implements_trait;
use rustc_lint::LateLintPass;
use rustc_session::{declare_lint_pass, declare_tool_lint};

use clippy_utils::diagnostics::span_lint_and_note;
use rustc_hir::{Expr, ExprKind};
use rustc_lint::LateContext;

use rustc_middle::ty::{Ty, TyKind};

use itertools::Itertools;

declare_clippy_lint! {
    /// ### What it does
    ///
    /// ### Why is this bad?
    ///
    /// ### Example
    /// ```rust
    /// // example code where clippy issues a warning
    /// ```
    /// Use instead:
    /// ```rust
    /// // example code which does not raise clippy warning
    /// ```
    #[clippy::version = "1.74.0"]
    pub PREVENT_HASH_MAP_ITERATIONS,
    nursery,
    "default sadjkmasdnjasdjk'[asdjkhasdkjhaskjhlkjhlkjlsanjDASnkasd]'sdnkjslint description"
}
declare_lint_pass!(PreventHashMapIterations => [PREVENT_HASH_MAP_ITERATIONS]);

pub const TYPES: [&str; 2] = ["HashSet", "HashMap"];
pub const FUNCTIONS: [&str; 3] = ["iter", "into_iter", "iter_mut"];

fn remove_brackets(input: &str) -> &str {
    match input.find('<') {
        Some(index) => &input[0..index],
        None => input,
    }
}

fn remove_module_name(input: &str) -> &str {
    input.split("::").last().unwrap_or(input)
}

fn get_expression_type<'a>(context: &LateContext<'a>, expression: &Expr<'a>) -> Ty<'a> {
    context.typeck_results().node_type(expression.hir_id)
}

fn get_name_of_type(a_type: Ty<'_>) -> String {
    remove_module_name(remove_brackets(a_type.to_string().as_str())).to_string()
}
fn is_result_enum(a_type: Ty<'_>) -> bool {
    // I couldn't find a better way to do it, but there might be on.
    // This is bad because TyKind might change, also what kind returns might change.
    #![allow(rustc::internal)]
    if let TyKind::Adt(adt_def, _) = a_type.kind() {
        if adt_def.is_enum() {
            let adt_name = format!("{adt_def:#?}");
            return "std::result::Result" == adt_name;
        }
    }

    false
}

fn peel_result(a_type: Ty<'_>) -> Ty<'_> {
    let mut walker = a_type.walk();
    // The first thing the walker yields is whole type.
    // The second is the actual subtype.
    walker.next();
    walker.next().unwrap().as_type().unwrap()
}

fn is_deref<'a>(context: &LateContext<'a>, a_type: Ty<'a>) -> bool {
    implements_trait(context, a_type, context.tcx.lang_items().deref_trait().unwrap(), &[])
}

fn peel_deref(a_type: Ty<'_>) -> Ty<'_> {
    // Here we are looking the the Target type of the deref.
    //
    // This walker returns a deep list of the sub types
    // If you have a map = Mutex<HashMap<u32, u32>
    // and you run map.lock().iter()
    // the type will be determained by map.lock()
    // and it will be std::sync::MutexGuard<'_, std::collections::HashMap<u32, u32>> wrapped Result
    // walking over the MutexGuard will first return the '_ and the the hashmap
    // but if the '_ was something else, something with nested types
    // then you will iterator over them.
    //
    // This is why we only want to iterate over the first layer of subtypes.
    // Sadly, there is no walk_shallow function, so we have to emulate one.
    // We run it in a loop because slip_current_subtree modifies the iterator
    // and thus cannot be called from inside of a map's hander.
    //
    // The walk return a GenericArg iterator, not a subtype iterator
    // a GenericArg might be a region, a const or an actall type.
    // In the MutexGuard example the '_ is returned and then the target type.
    //
    // What should be done is a function that analizes the Deref trait to figure
    // out the Target type. For example, maybe looking at the type's deref function's
    // return type (that should be the target type).
    // But I didn't find a way to do it correctly and im not going to spend more time on it.
    let mut walker = a_type.walk();
    // Like in peel_result the first thing walk yields is the whole type
    walker.next();
    loop {
        let current_item = walker.next();
        walker.skip_current_subtree();
        if let Some(argument) = current_item {
            if let Some(b_type) = argument.as_type() {
                break b_type;
            }
        } else {
            break a_type;
        }
    }
}

fn peel_type<'a>(context: &LateContext<'a>, a_type: Ty<'a>) -> Ty<'a> {
    peel_type_inner(0, context, a_type)
}

fn peel_type_inner<'a>(depth: u8, context: &LateContext<'a>, a_type: Ty<'a>) -> Ty<'a> {
    const RECURSION_LIMIT: u8 = 20;
    assert!(depth < RECURSION_LIMIT, "max recursion for type: {a_type:#?}");
    let a_type = a_type.peel_refs();
    let peedled_type = if is_result_enum(a_type) {
        peel_result(a_type)
    } else if is_deref(context, a_type) {
        peel_deref(a_type)
    } else {
        a_type
    };

    if peedled_type == a_type {
        peedled_type
    } else {
        peel_type_inner(depth + 1, context, peedled_type)
    }
}

impl<'tcx> LateLintPass<'tcx> for PreventHashMapIterations {
    fn check_expr(&mut self, context: &LateContext<'tcx>, expression: &'tcx Expr<'_>) {
        if let ExprKind::MethodCall(seg, receiver @ Expr { span, .. }, _, _) = expression.kind {
            if span.ctxt() == expression.span.ctxt() {
                let receiver_full_type = get_expression_type(context, receiver);
                let receiver_type = peel_type(context, receiver_full_type);
                let receiver_type_name = get_name_of_type(receiver_type);

                let function_name = seg.ident.name.as_str();

                for (bad_type, bad_function_name) in TYPES.iter().cartesian_product(FUNCTIONS.iter()) {
                    if *bad_type == receiver_type_name && *bad_function_name == function_name {
                        span_lint_and_note(
                            context,
                            PREVENT_HASH_MAP_ITERATIONS,
                            expression.span,
                            "Iterating over hashmaps is non-deterministic and unreproducible, use BTreeMap instead",
                            Some(*span),
                            format!("obejct has type {receiver_full_type}").as_str(),
                        );
                    }
                }
            }
        }
    }
}
