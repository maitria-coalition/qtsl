import DoubleCat.Basic
import DoubleCat.CellCategory
import DoubleCat.Sq
import DoubleCat.ImplDouble
import DoubleCat.Vert
import DoubleCat.JudgLayer
import DoubleCat.Virtual
import DoubleCat.Virtual.Functor
import DoubleCat.Virtual.OfPseudo
import DoubleCat.Virtual.FreePromotion
import DoubleCat.Virtual.Promote
import DoubleCat.Virtual.Grothendieck
import DoubleCat.Virtual.Opfibration
import DoubleCat.Virtual.GrothendieckRestrict
import DoubleCat.Virtual.Presentation
import DoubleCat.Functor.Lax
import DoubleCat.Functor.Composition
import DoubleCat.Functor.Whiskering
import DoubleCat.Functor.Pseudo
import DoubleCat.WireSpan
import DoubleCat.Opfibration
import DoubleCat.Transformation
import DoubleCat.LooseTransformation
import DoubleCat.Modification
import DoubleCat.Companion
import DoubleCat.CrossSite
import DoubleCat.Span
import DoubleCat.DepSpan
import DoubleCat.Grothendieck
import DoubleCat.Dbl
import DoubleCat.GrothendieckMap
import DoubleCat.GrothendieckBase
import DoubleCat.LooseBicategory
import DoubleCat.Monoidal
import DoubleCat.Monoidal.Strong
import DoubleCat.Monoidal.GradedCounterexample
import DoubleCat.Monoidal.GradedModel
import DoubleCat.Monoidal.Falsifiability
import DoubleCat.BagMonad

/-!
# Pseudo double categories

This library develops pseudo double categories: the core definition
(`DoubleCat.Basic`), the standard examples (commutative squares, spans,
type-valued matrices), lax double functors with their tight and loose
transformations and modifications, the strict 2-category and the pseudo
double category of lax double functors, companions, conjoints and proarrow
equipments, the double Grothendieck construction for span-valued lax double
functors, and monoidal double categories together with graded models
separating the coherence axioms — together with virtual double categories
(`DoubleCat.Virtual`): multicells over composable strings of loose arrows
with no loose composition assumed, their functors, the underlying virtual
double category of a pseudo double category, the free promotion of a
virtual double category to a pseudo double category, the virtual double
category of elements of a span-valued virtual functor, and discrete
virtual double opfibrations.

This module only re-exports the library.
-/

