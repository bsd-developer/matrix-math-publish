//! From decoded certificate payload to evaluable tree (spec §6.5, §17.7).
//!
//! §17.7 permits `mm-exact` to depend on core, rational, and schema types. The
//! bridge validates that each node's payload variant matches the variant its
//! position in the tree implies; the certificate's arrays are positional, so a
//! mismatch is a rejection rather than a reinterpretation (§5.2).

use crate::instance::OmegaInstance;
use crate::maxent::MaxEntropyBlock;
use crate::tree::{NodeVariables, TrackATree, skeleton};
use mm_core::codes::ErrorCode;
use mm_core::error::{CoreError, CoreResult};
use mm_core::path::NodeKind;
use mm_rat::log2::Precision;
use mm_schema::omega::{NodePayload, OmegaCertificate};

extern crate alloc;
use alloc::vec::Vec;

/// The evaluable form of a decoded omega certificate.
#[derive(Clone, Debug)]
pub struct EvaluableOmega {
    /// The instance tree with its free variables.
    pub tree: TrackATree,
    /// The maximum-entropy blocks, in certificate order.
    pub blocks: Vec<MaxEntropyBlock>,
    /// The validated target precision.
    pub precision: Precision,
}

/// Convert a decoded certificate into an evaluable tree and blocks.
///
/// # Errors
///
/// Returns [`ErrorCode::CountMismatch`] when the node count disagrees with the
/// instance tree and [`ErrorCode::BadPath`] when a node's payload variant
/// disagrees with its position.
pub fn from_certificate(certificate: &OmegaCertificate) -> CoreResult<EvaluableOmega> {
    let instance = OmegaInstance::new(certificate.q, certificate.level)?;
    let slots = skeleton(certificate.level)?;
    if slots.len() != certificate.nodes.len() {
        return Err(CoreError::new(
            ErrorCode::CountMismatch,
            "the node array length disagrees with the instance tree",
        )
        .equation("§6.5")
        .value(alloc::format!(
            "{} nodes, {} entries",
            slots.len(),
            certificate.nodes.len()
        )));
    }

    let mut variables = Vec::with_capacity(slots.len());
    for (slot, payload) in slots.iter().zip(certificate.nodes.iter()) {
        let converted = match (slot.kind, payload) {
            (
                NodeKind::Root,
                NodePayload::Branching {
                    region_weights,
                    alpha,
                },
            ) => NodeVariables::Root {
                region_weights: region_weights.clone(),
                alpha: alpha.clone(),
            },
            (
                NodeKind::PositiveInterior,
                NodePayload::Branching {
                    region_weights,
                    alpha,
                },
            ) => NodeVariables::Interior {
                region_weights: region_weights.clone(),
                alpha: alpha.clone(),
            },
            (NodeKind::ZeroShape, NodePayload::ZeroShape { beta }) => {
                NodeVariables::ZeroShape { beta: beta.clone() }
            }
            (NodeKind::PositiveLevelTwo, NodePayload::LevelTwo { mu }) => {
                NodeVariables::PositiveLevelTwo { mu: mu.clone() }
            }
            _ => {
                return Err(CoreError::new(
                    ErrorCode::BadPath,
                    "a node's payload variant disagrees with its position in the tree",
                )
                .equation("A.2")
                .value(slot.path.clone()));
            }
        };
        variables.push(converted);
    }

    let tree = TrackATree::new(instance, variables)?;
    let blocks = certificate
        .blocks
        .iter()
        .map(|block| MaxEntropyBlock {
            y: block.y.clone(),
            lambda0: block.lambda0.clone(),
            lambda_x: block.lambda_x.clone(),
            lambda_y: block.lambda_y.clone(),
            lambda_z: block.lambda_z.clone(),
            epsilon: block.epsilon.clone(),
        })
        .collect();
    let precision = Precision::new(certificate.log_precision_bits)?;
    Ok(EvaluableOmega {
        tree,
        blocks,
        precision,
    })
}
