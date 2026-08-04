import Qtsl.QArith
import Qtsl.Catalogue
import Qtsl.Farkas
import Qtsl.Decide
import Qtsl.ConeLemma
import Qtsl.EvalDemo
import Qtsl.Soundness
import Qtsl.SoundnessDemo
import Qtsl.Elaborators
import Qtsl.Comparator

import Qtsl.QArithCanon
import Qtsl.QArithKernel
import Qtsl.QArithLemmas

import Qtsl.Admissible

import Qtsl.PsdCert

import Qtsl.ReluExpansion
import Qtsl.PpolyExpansion
import Qtsl.DenotationClass
import Qtsl.DenotationGadgets
import Qtsl.DenotationCompile
import Qtsl.DenotationComplete
import Qtsl.MaskRegionAffine
import Qtsl.ShapePositions
import Qtsl.TensorNF
import Qtsl.PrimitiveBasisSoundWF
import Qtsl.PrimitiveBasisSoundX
import Qtsl.CellFlavors
import Qtsl.CellFlavorsDemo
import Qtsl.CellFlavorsExpansion
import Qtsl.CellFlavorsInterior
import Qtsl.CellFarkas
import Qtsl.CellFarkasDemo
import Qtsl.Substitution
import Qtsl.PackingGap
import Qtsl.HypernetCospan
import Qtsl.SubstitutionBridge
import Qtsl.SemOkRename
import Qtsl.ScmTwin

import Qtsl.Composition

import Qtsl.CoreBridge
import Qtsl.Core.DemoData

import Qtsl.Core.KernelReceipts

import Qtsl.IEEE754

import Qtsl.Handshake.CartpoleCoreDecrease
import Qtsl.Handshake.DpCompositeSyzygy
import Qtsl.Handshake.DpCompositeSmallGain

import Qtsl.Handshake.CartpoleControllerPinning

import Qtsl.Handshake.CartpoleMachineBridge

import Qtsl.ContractionRows

import Qtsl.ProductLattice

import Qtsl.QtslSoundness

import Qtsl.Discharge

import Qtsl.OrderAssembly

import Qtsl.EventualMember

import Qtsl.ChainRecurrence

import Qtsl.ChainMargin

import Qtsl.FacetRiding

import Qtsl.Crossing

import Qtsl.MeanValue

import Qtsl.OdeProfile

import Qtsl.PolyGradient

import Qtsl.RodeProfile

import Qtsl.DiniProfile

import Qtsl.GridGeometry

import Qtsl.Behavioral

import Qtsl.Switch

import Qtsl.Product

import Qtsl.LatticeInv

import Qtsl.Wire
import Qtsl.WireCheck
import Qtsl.WireSpec
import Qtsl.WireDemoData

import Qtsl.PderivExpansion
import Qtsl.FacetExpansion

import Qtsl.PoincareMiranda
import Qtsl.ChartPullback

import Qtsl.ReluSplit

import Qtsl.TimedCore
import Qtsl.Tabular
import Qtsl.Reach
import Qtsl.ReachContinuous
-- Plates: symbolic extents, T-PLATE / T-NAT / T-DESC
import Qtsl.Plate.Syntax
import Qtsl.Plate.TPlate
import Qtsl.Plate.Eval
import Qtsl.Plate.TNat
import Qtsl.Plate.TDesc
import Qtsl.Plate.Measure
import Qtsl.Plate.Probes
import Qtsl.Plate.TTransfer

/-!
# Bernstein Logic

Library root for the Lean development of Bernstein Logic: a certificate
calculus for polynomial inequality reasoning over hypernets, with an
executable checker whose computational core is independent of mathlib.

The development divides into:

* the certificate contract — data types, semantic model, and rounding
  theory (`Catalogue`, `Core/Catalogue`);
* exact arithmetic — rational, extended-rational, and dyadic-float
  kernels with their correctness theories (`QArith*`, `ERat`, `Dyadic`,
  `IEEE754`);
* per-rule soundness — every inhabitant of `ProofObject` witnesses
  semantic validity (`Soundness`, with the worked-example capstone in
  `SoundnessDemo`);
* the binary wire format — parser, declarative encoding relation, and
  first-order checker (`Wire`, `WireSpec`, `WireCheck`);
* composition and extension rules — assume–guarantee composition,
  context-carrying disjunction elimination, packaged-primitive
  expansion warrants (`Composition`, `Admissible`, `*Expansion`);
* QTSL dynamics — soundness lemmas for the temporal/dynamical rule
  family over semiflows and behavioural models (`Qtsl*`).
-/

