//! Backend semantics for the small set of runtime operations the compiler
//! understands beyond their surface types.
//!
//! Classification happens once, at the source/runtime boundary, by exact
//! qualified identity. Optimisation passes consume the attached metadata from
//! the lowered program; they must not rediscover semantics from mangled C names.

use crate::{ast::namer::QualifiedName, parser::IdentifierPath};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IntrinsicOperation {
    Ordinary,
    BytesSub,
    BytesGetU8,
    BytesGetU64Le,
    PackedArrayGetUnchecked,
    PackedArraySetUnchecked,
    Panic,
    RawPanic,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AllocationEffect {
    Never,
    Always,
    MayAllocate,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MemoryEffect {
    None,
    ReadOnly,
    Write,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ResultRepresentation {
    Ordinary,
    /// A fixed-size immutable slice descriptor whose fields are derived from
    /// arguments to the intrinsic. This is enough to emit the stack form
    /// without knowing the intrinsic's source name or calling convention.
    BorrowableSlice {
        owner_argument: usize,
        offset_argument: usize,
        length_argument: usize,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ControlFlow {
    Returns,
    NeverReturns,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CallFrequency {
    Normal,
    Cold,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct IntrinsicSemantics {
    pub operation: IntrinsicOperation,
    pub arity: usize,
    pub allocation: AllocationEffect,
    pub memory: MemoryEffect,
    pub result: ResultRepresentation,
    pub control_flow: ControlFlow,
    pub call_frequency: CallFrequency,
}

impl IntrinsicSemantics {
    pub fn c_attribute(self) -> &'static str {
        match (
            self.control_flow,
            self.call_frequency,
            self.memory,
            self.allocation,
        ) {
            (ControlFlow::NeverReturns, CallFrequency::Cold, _, _) => "MARM_NORETURN MARM_COLD ",
            (ControlFlow::NeverReturns, _, _, _) => "MARM_NORETURN ",
            (
                ControlFlow::Returns,
                _,
                MemoryEffect::None | MemoryEffect::ReadOnly,
                AllocationEffect::Never,
            ) => "MARM_PURE ",
            _ => "",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IntrinsicType {
    MutableArray,
}

fn module_is(path: &IdentifierPath, expected: &[&str]) -> bool {
    path.len() == expected.len()
        && expected
            .iter()
            .enumerate()
            .all(|(index, component)| path.element(index) == Some(*component))
}

fn semantics(
    operation: IntrinsicOperation,
    arity: usize,
    allocation: AllocationEffect,
    memory: MemoryEffect,
    result: ResultRepresentation,
    control_flow: ControlFlow,
) -> IntrinsicSemantics {
    IntrinsicSemantics {
        operation,
        arity,
        allocation,
        memory,
        result,
        control_flow,
        call_frequency: CallFrequency::Normal,
    }
}

/// Identify a compiler-known term. This is the only place where stdlib names
/// acquire backend meaning, and comparisons are exact qualified-name matches.
pub fn term(name: &QualifiedName) -> Option<IntrinsicSemantics> {
    let member = name.member.as_str();

    if module_is(&name.module, &["Root", "Prelude", "Bytes"]) {
        if member == "raw_sub" {
            return Some(semantics(
                IntrinsicOperation::BytesSub,
                3,
                AllocationEffect::Always,
                MemoryEffect::ReadOnly,
                ResultRepresentation::BorrowableSlice {
                    owner_argument: 0,
                    offset_argument: 1,
                    length_argument: 2,
                },
                ControlFlow::Returns,
            ));
        }
        if matches!(
            member,
            "raw_position"
                | "raw_slice_len"
                | "raw_get_u8"
                | "raw_get_u16_le"
                | "raw_get_u32_le"
                | "raw_get_u64_le"
                | "raw_get_i16_le"
                | "raw_get_i32_le"
                | "raw_get_i64_le"
                | "raw_get_u16_be"
                | "raw_get_u32_be"
                | "raw_get_u64_be"
                | "raw_get_i16_be"
                | "raw_get_i32_be"
                | "raw_get_i64_be"
                | "raw_is_valid"
        ) {
            let arity = if member == "raw_position" {
                3
            } else if member == "raw_slice_len" || member == "raw_is_valid" {
                1
            } else {
                2
            };
            let operation = match member {
                "raw_get_u8" => IntrinsicOperation::BytesGetU8,
                "raw_get_u64_le" => IntrinsicOperation::BytesGetU64Le,
                _ => IntrinsicOperation::Ordinary,
            };
            return Some(semantics(
                operation,
                arity,
                AllocationEffect::Never,
                MemoryEffect::ReadOnly,
                ResultRepresentation::Ordinary,
                ControlFlow::Returns,
            ));
        }
    }

    if module_is(
        &name.module,
        &["Root", "Stdlib", "Data", "Array", "Mutable_Array"],
    ) {
        if member == "raw_len" {
            return Some(semantics(
                IntrinsicOperation::Ordinary,
                1,
                AllocationEffect::Never,
                MemoryEffect::ReadOnly,
                ResultRepresentation::Ordinary,
                ControlFlow::Returns,
            ));
        }
        let operation = match member {
            "raw_get_unchecked" => IntrinsicOperation::PackedArrayGetUnchecked,
            "raw_set_unchecked" => IntrinsicOperation::PackedArraySetUnchecked,
            _ => return None,
        };
        return Some(semantics(
            operation,
            if operation == IntrinsicOperation::PackedArrayGetUnchecked {
                2
            } else {
                3
            },
            AllocationEffect::MayAllocate,
            if operation == IntrinsicOperation::PackedArrayGetUnchecked {
                MemoryEffect::ReadOnly
            } else {
                MemoryEffect::Write
            },
            ResultRepresentation::Ordinary,
            ControlFlow::Returns,
        ));
    }

    if module_is(&name.module, &["Root", "Stdlib", "Data", "Array", "Array"]) && member == "raw_len"
    {
        return Some(semantics(
            IntrinsicOperation::Ordinary,
            1,
            AllocationEffect::Never,
            MemoryEffect::ReadOnly,
            ResultRepresentation::Ordinary,
            ControlFlow::Returns,
        ));
    }

    if module_is(&name.module, &["Root", "Prelude"]) {
        let (operation, arity) = match member {
            "omg_wtf_bbq" => (IntrinsicOperation::Panic, 1),
            "raw_omg_wtf_bbq" => (IntrinsicOperation::RawPanic, 5),
            _ => return None,
        };
        let mut semantics = semantics(
            operation,
            arity,
            AllocationEffect::Never,
            MemoryEffect::Write,
            ResultRepresentation::Ordinary,
            ControlFlow::NeverReturns,
        );
        semantics.call_frequency = CallFrequency::Cold;
        return Some(semantics);
    }

    None
}

pub fn intrinsic_type(name: &QualifiedName) -> Option<IntrinsicType> {
    (module_is(&name.module, &["Root", "Stdlib", "Data", "Array"])
        && name.member.as_str() == "Mutable_Array")
        .then_some(IntrinsicType::MutableArray)
}

pub fn raw_panic_name() -> QualifiedName {
    let module = IdentifierPath::new("Root").with_suffix("Prelude");
    QualifiedName::new(module, "raw_omg_wtf_bbq")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn qualified(module: &[&str], member: &str) -> QualifiedName {
        let mut path = IdentifierPath::new(module[0]);
        for component in &module[1..] {
            path.push(component);
        }
        QualifiedName::new(path, member)
    }

    #[test]
    fn classification_is_exact_not_a_mangled_suffix_match() {
        let real = qualified(&["Root", "Prelude", "Bytes"], "raw_sub");
        assert_eq!(
            term(&real).map(|semantics| semantics.operation),
            Some(IntrinsicOperation::BytesSub)
        );

        let lookalike = qualified(&["Root", "Fake", "Prelude", "Bytes"], "raw_sub");
        assert_eq!(term(&lookalike), None);
    }
}
