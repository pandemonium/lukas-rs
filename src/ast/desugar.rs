use crate::{
    ast::{self, Tuple, namer::Symbol},
    parser::{IdentifierPath, ParseInfo, Parsed},
    phase,
};

pub struct Desugared;

impl phase::Phase for Desugared {
    type Annotation = ParseInfo;
    type TermId = IdentifierPath;
    type TypeId = IdentifierPath;
}

type Expr = phase::Expr<Desugared>;

impl phase::Expr<Parsed> {
    pub fn lower_tuples(self) -> phase::Expr<Parsed> {
        self.map(&mut |e| match e {
            ast::Expr::Tuple(a, tuple) => ast::Expr::Tuple(
                a,
                Tuple {
                    elements: unspine_tuple(tuple.elements),
                },
            ),
            otherwise => otherwise,
        })
    }

    pub fn desugar(&self) -> Expr {
        self.clone().lower_tuples()
    }
}

fn unspine_tuple(
    elements: Vec<ast::Tree<ParseInfo, IdentifierPath>>,
) -> Vec<ast::Tree<ParseInfo, IdentifierPath>> {
    elements
        .into_iter()
        .flat_map(|e| match (*e).clone() {
            // This is probably not correct - it flattens too much
            ast::Expr::Tuple(_, tuple) => unspine_tuple(tuple.elements.to_vec()),
            atom => vec![atom.into()],
        })
        .collect()
}

impl phase::SymbolTable<Parsed> {
    // Can't I just rewrite the whole table like with resolve_names?
    // This way I could probably remove the annoying TermSymbol::body
    pub fn desugar_expressions(&mut self) {
        for symbol in self.symbols.values_mut() {
            if let Symbol::Term(symbol) = symbol {
                let body = symbol
                    .body
                    .take()
                    .expect("Internal Assertion - expected a symbol body.");
                symbol.body = body.desugar().into();
            }
        }
    }

    pub fn rewrite_pattern_introductions(&mut self) {}

    pub fn desugar(&self) -> phase::SymbolTable<Desugared> {
        println!("desugar: running");

        let mut symbols = self.clone();
        symbols.desugar_expressions();

        symbols
    }
}
