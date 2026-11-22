import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2752
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2627
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2337
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0036
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValueStatementHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2753
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2746
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2754
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0478
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0481
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0480
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2570
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsChernExistsUniqueAndIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0482
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2757
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2739
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicFrobeniusPointComparisonStatement
section
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open scoped NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel GlobalTheory.Toroidal
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm
open GlobalTheory.DetHT
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.ShFam.Descent

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.p_adic_frobenius_point_comparison : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F))
    (p : ℕ) [Fact p.Prime] [Algebra c.F ℂ_[p]] (P z : FrPt Xo c ℂ_[p]) (yb : Sp 𝓞_ℂ_[p] ⟶ Z.X),
    GlobalTheory.AllWt.ptF z = GlobalTheory.AllWt.ptF P →
    letI := H.starRing; ∀ (Q : PtP E p) (π : Q.G.left ⟶ Z.t.G.left) (ψ : Q.A.A.left ⟶ Z.oF.t.G.left),
      PtAt Z yb (GlobalTheory.AllWt.ptF P) Q π ψ → ∀ (σ : E →+* ℂ) (j : Fin (Dw.mult σ)) (xx : LieG Q.Gt),
      LieTie Q (ψ ≫ Z.m0.toSABMap.φ) xx (z.u σ j) → LieTie Q (Q.gen ≫ π) xx ((frameOf Z z).v σ j) := by
  first | exact @GlobalTheory.DetHT.lieTie_frameOf_of_ptAt | exact GlobalTheory.DetHT.lieTie_frameOf_of_ptAt | (intros; apply GlobalTheory.DetHT.lieTie_frameOf_of_ptAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicPointLatticeEvaluationStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.p_adic_point_lattice_evaluation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l' : Level H)
    (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (p : ℕ)
    [Fact p.Prime] (n : ℕ) [StarRing (𝓞 E)] (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p)
    (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left), PtOn Y yb yy P π ψ → ∀ (a : Dw.La) (tt : P.T),
    (tt.lev n).left ≫ ψ = yy ≫ (Y.oF.etaA a).left → ∀ (z : GlobalTheory.ChTor.Pts P.A.A) (e σ : Over.mk yy ⟶ Y.oF.t.G),
    e.left = yy ≫ (Y.oF.etaA a).left → σ.left = z.left ≫ ψ → σ ^ (p ^ n) = 1 → ∀ c : ℂ_[p]ˣ,
    Out.WeilIs Y.oF.t.G Y.oF.t.PP.L ((p ^ n : ℕ) : ℤ) e σ (unitOn c) → (c : ℂ_[p]) = (weil P.A (p ^ n) (tt.lev n) z : ℂ_[p]) := by
  first | exact @GlobalTheory.ModelPointWeil.weil_eq_of_weilIs_model | exact GlobalTheory.ModelPointWeil.weil_eq_of_weilIs_model | (intros; apply GlobalTheory.ModelPointWeil.weil_eq_of_weilIs_model <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicPointPeriodRelationStatement
section
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open scoped NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel GlobalTheory.Toroidal
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm
open GlobalTheory.DetHT
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.ShFam.Descent

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.p_adic_point_period_relation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F))
    (p : ℕ) [Fact p.Prime] [Algebra c.F ℂ_[p]] (z : FrPt Xo c ℂ_[p]) (yb : Sp 𝓞_ℂ_[p] ⟶ Z.X)
    (yy : Sp ℂ_[p] ⟶ Xo.XF c),
    letI := H.starRing; ∀ (Q : PtP E p) (π : Q.G.left ⟶ Z.t.G.left) (ψ : Q.A.A.left ⟶ Z.oF.t.G.left),
      PtAt Z yb yy Q π ψ → ∀ (σ : E →+* ℂ) (j : Fin (Dw.mult σ)) (xx : LieG Q.Gt),
      LieTie Q (ψ ≫ Z.m0.toSABMap.φ) xx (z.u σ j) → AvDefs.IsEig Q.Gt Q.oGt (embInt c Q.integers σ) xx := by
  first | exact @GlobalTheory.DetHT.ptAt_tangent_isEig | exact GlobalTheory.DetHT.ptAt_tangent_isEig | (intros; apply GlobalTheory.DetHT.ptAt_tangent_isEig <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicPointTangentMapFormulaStatement
section
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open scoped NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel GlobalTheory.Toroidal
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm
open GlobalTheory.DetHT
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.ShFam.Descent

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.p_adic_point_tangent_map_formula : BridgeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F))
    (p : ℕ) [Fact p.Prime] [Algebra c.F ℂ_[p]] (yy : Sp ℂ_[p] ⟶ Xo.XF c) (yb : Sp 𝓞_ℂ_[p] ⟶ Z.X),
    letI := H.starRing; ∀ (Q : PtP E p) (π : Q.G.left ⟶ Z.t.G.left) (ψ : Q.A.A.left ⟶ Z.oF.t.G.left),
      PtAt Z yb yy Q π ψ → ∀ (n : ℕ) (xx : Fin n → LieG Q.Gt) (u u' : Fin n → (Sp (DualNumber ℂ_[p]) ⟶ Z.t.G.left))
      (g : Matrix (Fin n) (Fin n) ℂ_[p]), (∀ j, IsTanAtG Z.t (yy ≫ Z.j) (u j)) →
      (∀ j, LieTie Q (Q.gen ≫ π) (xx j) (u j)) → (∀ i, IsCombAtG Z.t (yy ≫ Z.j) u (g i) (u' i)) →
      ∀ (a : Fin n → ℂ_[p]) (w : Sp (DualNumber ℂ_[p]) ⟶ Z.t.G.left), IsCombAtG Z.t (yy ≫ Z.j) u' a w →
        (w ∈ GlobalTheory.ShFam.Pad.latHT Z.t p (yy ≫ Z.j) ↔ ∑ i, a i • ∑ j, g i j • Q.bLie (xx j) ∈ Q.latT) := by
  first | exact @GlobalTheory.DetHT.BridgeBasis.mem_latHT_iff_changeBasis | exact GlobalTheory.DetHT.BridgeBasis.mem_latHT_iff_changeBasis | (intros; apply GlobalTheory.DetHT.BridgeBasis.mem_latHT_iff_changeBasis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairData
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RootFrameB

def colMinor {K : Type} [CommRing K] {n r : ℕ} (X : Matrix (Fin n) (Fin r) K) (k : ℕ) (hk : k ≤ r) (σ : Fin k → Fin n) : K :=
  (Matrix.of fun a l : Fin k => X (σ a) (Fin.castLE hk l)).det

def lo {r s N : ℕ} (h : r + s = N) (i : Fin r) : Fin N := ⟨i, by omega⟩

def hi {r s N : ℕ} (h : r + s = N) (l : Fin s) : Fin N := ⟨N - 1 - l, by omega⟩

section Cover

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

def Tst (V : Cover Y) (W : Y.X.Opens) (p : ℕ) (v : HeightOneSpectrum (𝓞 F)) (e : TrueGeo.Ext v) (y : AlgPt Y)
    (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X) : Prop :=
  resP v = p ∧ below y.1 ∈ W ∧ z ≫ V.π = y.1 ∧ spMap e.O.subtype ≫ yt = z ≫ V.j

def vals (V : Cover Y) {n r : ℕ} (X : Matrix (Fin n) (Fin r) V.G.functionField) (T : Y.X → Matrix (Fin r) (Fin r) Y.Fn)
    (z : Sp (AlgebraicClosure F) ⟶ V.G) (x : Y.X) : Matrix (Fin n) (Fin r) (AlgebraicClosure F) :=
  (X * ((T x).map V.φ)⁻¹).map (TrueGeo.valAt z)

def PowRead (V : Cover Y) (p : ℕ) (f : Y.X → Y.Fn) (l : PtFn Y) : Prop :=
  ∃ m : ℕ, 0 < m ∧ ∀ x : V.X, ¬ IsUnit (p : V.X.presheaf.stalk x) → ∃ (U : V.X.Opens) (r : V.G.functionField), x ∈ U ∧
    (∀ z : V.G, V.j z ∈ U → UnitAt z (V.φ (f (V.π z)) ^ m * r)) ∧
    ∀ v e y z yt, Tst V ⊤ p v e y z yt → ⊤ ≤ yt ⁻¹ᵁ U →
      m * l v e y = Real.log (e.w (TrueGeo.valAt z (V.φ (f (below y.1)) ^ m * r)))

def SideData (V : Cover Y) (W : Y.X.Opens) (p : ℕ) {J : Type} (U : J → V.X.Opens) {n r : ℕ}
    (X : J → Matrix (Fin n) (Fin r) V.G.functionField) (T : Y.X → Matrix (Fin r) (Fin r) Y.Fn)
    (f : Fin r → Y.X → Y.Fn) (l : Fin r → PtFn Y) : Prop :=
  (∀ x, (T x).BlockTriangular id ∧ ∀ i, UnitAt x (f i x * T x i i)) ∧
  (∀ a (z : V.G), V.j z ∈ U a → ∀ k i, RegAt z ((X a * ((T (V.π z)).map V.φ)⁻¹) k i)) ∧
  ∀ v e y z yt, Tst V W p v e y z yt → ∃ ν : ℕ → ℝ, (∀ k, k ≤ r → 0 < ν k) ∧
    (∀ i : Fin r, l i v e y = Real.log (e.w (TrueGeo.valAt y.1 (f i (below y.1) * T (below y.1) i i))) +
      Real.log (ν ((i : ℕ) + 1)) - Real.log (ν (i : ℕ))) ∧
    ∀ a, ⊤ ≤ yt ⁻¹ᵁ U a →
      (∀ k (hk : k ≤ r) σ, e.w (colMinor (vals V (X a) T z (below y.1)) k hk σ) ≤ ν k) ∧
      (∀ k (hk : k ≤ r), ∃ σ, e.w (colMinor (vals V (X a) T z (below y.1)) k hk σ) = ν k) ∧
      ∀ b, ⊤ ≤ yt ⁻¹ᵁ U b → ∀ u : Fin r → AlgebraicClosure F, (∀ k, e.w ((vals V (X a) T z (below y.1) *ᵥ u) k) ≤ 1) →
        ∀ k, e.w ((vals V (X b) T z (below y.1) *ᵥ u) k - (vals V (X a) T z (below y.1) *ᵥ u) k) < 1

def Orth (V : Cover Y) (W : Y.X.Opens) (p : ℕ) {J : Type} (U : J → V.X.Opens) {n r s : ℕ}
    (X : J → Matrix (Fin n) (Fin r) V.G.functionField) (T : Y.X → Matrix (Fin r) (Fin r) Y.Fn)
    (X' : J → Matrix (Fin n) (Fin s) V.G.functionField) (T' : Y.X → Matrix (Fin s) (Fin s) Y.Fn) : Prop :=
  ∀ v e y z yt, Tst V W p v e y z yt → ∀ a, ⊤ ≤ yt ⁻¹ᵁ U a →
    ∀ (u : Fin r → AlgebraicClosure F) (u' : Fin s → AlgebraicClosure F),
      (∀ k, e.w ((vals V (X a) T z (below y.1) *ᵥ u) k) ≤ 1) → (∀ k, e.w ((vals V (X' a) T' z (below y.1) *ᵥ u') k) ≤ 1) →
      e.w ((vals V (X a) T z (below y.1) *ᵥ u) ⬝ᵥ (vals V (X' a) T' z (below y.1) *ᵥ u')) < 1

def FrameOn (V : Cover Y) (W : Y.X.Opens) (p : ℕ) (U : V.X.Opens) {n r : ℕ}
    (X : Matrix (Fin n) (Fin r) V.G.functionField) (T : Y.X → Matrix (Fin r) (Fin r) Y.Fn)
    (f : Fin r → Y.X → Y.Fn) (l : Fin r → PtFn Y) (M : Matrix (Fin n) (Fin r) V.X.functionField)
    (c : Fin r → V.G.functionFieldˣ) (σ : Fin r → Fin n) : Prop :=
  (∀ x ∈ U, ¬ IsUnit (p : V.X.presheaf.stalk x) → ∀ k i, RegAt x (M k i)) ∧ (M.submatrix σ id).det = 1 ∧
  (∀ i (z : V.G), V.j z ∈ U → UnitAt z (V.φ (f i (V.π z)) * c i)) ∧
  ∀ v e y z yt, Tst V W p v e y z yt → ⊤ ≤ yt ⁻¹ᵁ U →
    (∀ i, l i v e y = Real.log (e.w (TrueGeo.valAt z (V.φ (f i (below y.1)) * (c i : V.G.functionField))))) ∧
    ∃ β : Matrix (Fin r) (Fin r) (AlgebraicClosure F), β.BlockTriangular id ∧
      M.map (TrueGeo.valAt (z ≫ V.j)) = vals V X T z (below y.1) * β ∧
      ∀ i, β i i * TrueGeo.valAt z (V.φ (f i (below y.1)) * (c i : V.G.functionField)) =
        TrueGeo.valAt y.1 (f i (below y.1) * T (below y.1) i i)

def PairData {C : CxSt F} {N : ℕ} (A : Fin N → Adl C Y) (p : ℕ) : Prop :=
  ∃ (V : Cover Y) (W : Y.X.Opens) (J : Type) (U : J → V.X.Opens) (r s : ℕ) (h : r + s = N)
    (X : J → Matrix (Fin N) (Fin r) V.G.functionField) (T : Y.X → Matrix (Fin r) (Fin r) Y.Fn)
    (X' : J → Matrix (Fin N) (Fin s) V.G.functionField) (T' : Y.X → Matrix (Fin s) (Fin s) Y.Fn),
    genericPoint Y.X ∈ W ∧ (∀ x : V.X, ¬ IsUnit (p : V.X.presheaf.stalk x) → ∃ a, x ∈ U a) ∧
    (∀ i, PowRead V p (genAt (A i).D) (A i).lg) ∧
    SideData V W p U X T (fun i => genAt (A (lo h i)).D) (fun i => (A (lo h i)).lg) ∧
    SideData V W p U X' T' (fun i x => (genAt (A (hi h i)).D x)⁻¹) (fun i v e y => -(A (hi h i)).lg v e y) ∧
    Orth V W p U X T X' T'

end Cover

section Chars

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def IsLabel (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {R : Type} [CommRing R] (y : Sp R ⟶ Xo.XF c) (q : ℕ)
    (lb : Dw.La → (Over.mk y ⟶ Z.oF.t.G)) (ζ : Rˣ) : Prop :=
  IsPrimitiveRoot ζ q ∧ (∀ a b, lb (a + b) = lb a * lb b) ∧ (∀ (o : 𝓞 E) a, lb (o • a) = lb a ≫ Z.oF.t.act.act o) ∧
    (∀ a, lb a ^ q = 1) ∧ ∀ a b, Out.WeilIs Z.oF.t.G Z.oF.t.PP.L (q : ℤ) (lb a) (lb b) (unitOn (ζ ^ Dw.EF a b))

def WeilLab (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {p : ℕ} [Fact p.Prime] (x : Sp ↥(intO ℂ_[p]) ⟶ Z.X)
    (y : Sp ℂ_[p] ⟶ Xo.XF c) (q : ℕ) (ch : Dw.La → TorsChar Z.t x q) : Prop :=
  ∃ (lb : Dw.La → (Over.mk y ⟶ Z.oF.t.G)) (ζ : ℂ_[p]ˣ), IsLabel Z y q lb ζ ∧
    ∀ a (w : Over.mk (spMap (algebraMap ↥(intO ℂ_[p]) ↥(intO ℂ_[p])) ≫ x) ⟶ Z.t.G) (σ : Over.mk y ⟶ Z.oF.t.G),
      w ^ q = 1 → σ.left ≫ Z.m.φ = spMap (intO ℂ_[p]).subtype ≫ w.left →
      Out.WeilIs Z.oF.t.G Z.oF.t.PP.L (q : ℤ) (lb a) σ
        (unitOn (Units.map (intO ℂ_[p]).subtype.toMonoidHom ((ch a).χ ↥(intO ℂ_[p]) w)))

def LabFam (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {S : Scheme.{0}} (ρ : S ⟶ Z.X) (p : ℕ) [Fact p.Prime] (n : ℕ) : Prop :=
  ∃ ch : Dw.La → ∀ x : Sp ↥(intO ℂ_[p]) ⟶ S, TorsChar Z.t (x ≫ ρ) (p ^ n),
    (∀ x (y : Sp ℂ_[p] ⟶ Xo.XF c), spMap (intO ℂ_[p]).subtype ≫ x ≫ ρ = y ≫ Z.j →
      WeilLab Z (x ≫ ρ) y (p ^ n) fun a => ch a x) ∧
    ∀ (U : S.Opens) (hU : IsAffineOpen U) (g : ℕ) (e : Fin g → (Sp (DualNumber Γ(S, U)) ⟶ Z.t.G.left)),
      IsTanBasis Z.t (R := Γ(S, U)) (hU.fromSpec ≫ ρ) e → ∃ h : Dw.La → Fin g → Γ(S, U),
        ∀ (φ : Γ(S, U) →+* ↥(intO ℂ_[p])) (x : Sp ↥(intO ℂ_[p]) ⟶ S), spMap φ ≫ hU.fromSpec = x →
          ∀ a, DlogIs Z.t p n (ch a x) (fun i => spMap (dualMap φ) ≫ e i) (fun i => φ (h a i))

variable (Dw) in

def pr {K : Type} [CommRing K] (y : K ⊗[ℤ] Dw.La) (a : Dw.La) : K := Dw.EF.baseChange K y (1 ⊗ₜ a)

variable (Dw) in

def IsEigL {K : Type} [CommRing K] (σ : 𝓞 E →+* K) (y : K ⊗[ℤ] Dw.La) : Prop :=
  ∀ o : 𝓞 E, ((LinearMap.lsmul (𝓞 E) Dw.La o).restrictScalars ℤ).baseChange K y = σ o • y

variable (Dw) in

def HTLin {X : Scheme.{0}} (t : SAB H X) (p : ℕ) [Fact p.Prime] (n : ℕ) (x : Sp ↥(intO ℂ_[p]) ⟶ X)
    (ch : Dw.La → TorsChar t x (p ^ n)) {g : ℕ} (e : Fin g → (Sp (DualNumber ↥(intO ℂ_[p])) ⟶ t.G.left))
    (b : (Fin g → ℂ_[p]) →ₗ[ℂ_[p]] ℂ_[p] ⊗[ℤ] Dw.La) : Prop :=
  (∀ a (h : Fin g → ↥(intO ℂ_[p])), DlogIs t p n (ch a) e h →
    ∀ i, ‖(h i : ℂ_[p]) - pr Dw (b (Pi.single i 1)) a‖ ≤ (p : ℝ)⁻¹ ^ n) ∧
  (∀ cf w, IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ x) (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ e i) cf w →
    (w ∈ latHT t p (spMap (intO ℂ_[p]).subtype ≫ x) ↔ ∀ a, ‖pr Dw (b cf) a‖ ≤ 1) ∧
    ∀ σ : 𝓞 E →+* ℂ_[p], GlobalTheory.FlatModel.IsEigG t σ w → IsEigL Dw σ (b cf)) ∧
  ∀ cf cf', (∀ a, ‖pr Dw (b cf) a‖ ≤ 1) → (∀ a, ‖pr Dw (b cf') a‖ ≤ 1) →
    ‖Dw.EF.baseChange ℂ_[p] (b cf) (b cf')‖ ≤ (p : ℝ)⁻¹ ^ n

variable (Dw) in

def CutL {K : Type} [NormedField K] (σ : 𝓞 E →+* K) {M N : ℕ} (a : Fin M → Dw.La) (T : Fin N → Fin M → K) (δ : K) : Prop :=
  (∀ j m, ‖T j m‖ ≤ 1) ∧ ∀ y, IsEigL Dw σ y → ((∀ j, ‖∑ m, T j m * pr Dw y (a m)‖ ≤ 1) ↔ ∀ b, ‖δ * pr Dw y b‖ ≤ 1)

variable (Dw) in

def DualL {K : Type} [CommRing K] (σ σ' : 𝓞 E →+* K) {M N : ℕ} (a : Fin M → Dw.La) (T S : Fin N → Fin M → K) : Prop :=
  ∀ y y', IsEigL Dw σ y → IsEigL Dw σ' y' →
    ∑ j, (∑ m, T j m * pr Dw y (a m)) * (∑ m, S j m * pr Dw y' (a m)) = -Dw.EF.baseChange K y y'

end Chars

section Cut

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

def CutBy {C : Type} [NormedField C] (x : Sp C ⟶ X) (Λ : Set (Sp (DualNumber C) ⟶ t.G.left)) {n r : ℕ}
    (u : Fin r → (Sp (DualNumber C) ⟶ t.G.left)) (P : Matrix (Fin n) (Fin r) C) (δ : C) : Prop :=
  (∀ cf, P *ᵥ cf = 0 → cf = 0) ∧ ∀ cf w, IsCombAtG t x u cf w → (w ∈ Λ ↔ ∀ k, ‖(P *ᵥ cf) k‖ ≤ ‖δ‖)

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

def CutAt (V : Cover Y) (W : Y.X.Opens) (p : ℕ) (ρ : Y.X ⟶ X) {J : Type} (U : J → V.X.Opens) {n r : ℕ}
    (f : ∀ y : Y.X, Fin r → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left))
    (P : J → Matrix (Fin n) (Fin r) V.G.functionField) (T : Y.X → Matrix (Fin r) (Fin r) Y.Fn) (κ : ℝ) : Prop :=
  ∀ v e y z yt, Tst V W p v e y z yt → ∀ [Fact (resP v).Prime], ∃ δ : ℂ_[resP v], δ ≠ 0 ∧
    Real.log ‖δ‖ = -(κ * Real.log (resP v)) ∧ ∀ a, ⊤ ≤ yt ⁻¹ᵁ U a →
      CutBy t (spMap ((ioOf (resP v) e).comp (Scheme.stalkClosedPointTo y.1).hom) ≫ stalkPt Y (below y.1) ≫ ρ)
        (latHT t (resP v)
          (spMap ((ioOf (resP v) e).comp (Scheme.stalkClosedPointTo y.1).hom) ≫ stalkPt Y (below y.1) ≫ ρ))
        (fun i => spMap (dualMap ((ioOf (resP v) e).comp (Scheme.stalkClosedPointTo y.1).hom)) ≫ f (below y.1) i)
        ((vals V (P a) T z (below y.1)).map (ioOf (resP v) e)) δ ∧
      ∀ b, ⊤ ≤ yt ⁻¹ᵁ U b → ∀ u : Fin r → ℂ_[resP v],
        (∀ k, ‖((vals V (P a) T z (below y.1)).map (ioOf (resP v) e) *ᵥ u) k‖ ≤ 1) →
        ∀ k, ‖((vals V (P b) T z (below y.1)).map (ioOf (resP v) e) *ᵥ u) k -
          ((vals V (P a) T z (below y.1)).map (ioOf (resP v) e) *ᵥ u) k‖ < 1

end Cut

def covMat {K : Type} [CommRing K] {M N g r : ℕ} (T : Fin N → Fin M → K) (h : Fin M → Fin g → K) (A : Fin r → Fin g → K) :
    Matrix (Fin N) (Fin r) K :=
  Matrix.of fun j i => ∑ m, T j m * ∑ k, h m k * A i k

end GlobalTheory.RootFrameB

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairSectionMemBallExpOfProjArithVarietyStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairSection_mem_ball_exp_of_projArithVariety : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (a b : ℤ) (f : X.functionField), f ∈ P.H a b → ∃ u : ℝ, 0 ≤ u ∧ f ∈ P.Bl a b (Real.exp u) := by
  first | exact @GlobalTheory.HSNef.bounded_norm | exact GlobalTheory.HSNef.bounded_norm | (intros; apply GlobalTheory.HSNef.bounded_norm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairSectionsFgOfProjArithVarietyStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairSections_fg_of_projArithVariety : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (a b : ℤ), (P.H a b).FG := by
  first | exact @GlobalTheory.HSNef.PairFG.h_fg | exact GlobalTheory.HSNef.PairFG.h_fg | (intros; apply GlobalTheory.HSNef.PairFG.h_fg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairingEigenspaceOrthogonal
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Div.PairingEigenspaceOrthogonal

theorem pairing_eig_orth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ →
    ∀ (R : Type) [CommRing R] (K : Type) [Field K] [Algebra R K] (H : Type) [AddCommGroup H] [Module R H]
    (I : Type) (φ : I → E →+* K) (ρ : orderC c →+* Module.End R H) (Fil : Submodule R H) (B : LinearMap.BilinForm R H),
    GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsCMLattice φ ρ Fil B → ∀ σ σ' : E →+* K, σ' ≠ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar σ →
    ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ σ, ∀ y ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ σ', B.baseChange K x y = 0 := by
  intro E _ _ _ c hc R _ K _ _ H _ _ I φ ρ Fil B hL σ σ' hne x hx y hy
  have hadj := hL.2.2.2.2.2.2.2.2

  have hne' : σ ≠ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar σ' := by
    intro h; apply hne; rw [h]; ext z; simp [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar, IsCMField.complexConj_apply_apply]
  obtain ⟨a, ha⟩ : ∃ a : orderC c, σ a ≠ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar σ' a := by
    by_contra hall; push_neg at hall
    exact hne' (GlobalTheory.EigLineSum.ringHom_eq_of_eq_on_orderC hc hall)
  let b : orderC c := ⟨IsCMField.complexConj E (a : E), GlobalTheory.LatModel.HalfFormUnit.conj_mem_orderC a.2⟩
  have hK : ∀ u v : K ⊗[R] H, B.baseChange K ((ρ a).baseChange K u) v = B.baseChange K u ((ρ b).baseChange K v) := by
    intro u v
    induction u using TensorProduct.induction_on with
    | zero => simp
    | add u1 u2 h1 h2 => simp only [map_add, LinearMap.add_apply, h1, h2]
    | tmul r m =>
      induction v using TensorProduct.induction_on with
      | zero => simp
      | add v1 v2 h1 h2 => simp only [map_add, h1, h2]
      | tmul r' m' =>
        simp only [LinearMap.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul]
        rw [hadj a b rfl m m']
  have h1 := hK x y
  rw [GlobalTheory.LowerOps.act_of_mem_eigK hx a, GlobalTheory.LowerOps.act_of_mem_eigK hy b] at h1
  simp only [LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul] at h1
  have hb : σ' (b : E) = GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar σ' a := rfl
  rw [hb] at h1
  have h2 : (σ a - GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar σ' a) * B.baseChange K x y = 0 := by rw [sub_mul, h1, sub_self]
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 ha)

end GlobalTheory.Div.PairingEigenspaceOrthogonal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairingKernelTrivial
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

theorem GlobalTheory.Mum.pairing_kernel_trivial : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → ∀ (T : Over (Sp (FractionRing R))) (x : T ⟶ ((Over.pullback (jK R)).obj G)), (∃ t : LB.Gen ((((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull κ₀).pull (lift (snd ((Over.pullback (jK R)).obj G) T ≫ x) (fst ((Over.pullback (jK R)).obj G) T) : ((Over.pullback (jK R)).obj G) ⊗ T ⟶ G2 ((Over.pullback (jK R)).obj G)).left), t.IsGen) → x = toUnit T ≫ η[((Over.pullback (jK R)).obj G)] := by
  intro R _ _ _ hR D D' F hF A' G' _ _ hG' U' oA oG hlin G _ _ hG inc pr hinc hpr hip hpi κ₀ hκ T x hx
  have h1 := GlobalTheory.T.pull_generator_factor_pairing_generic_mumfordBundle R D D' F A' G' U' oA oG hlin G inc hinc κ₀ hκ T x hx
  have hra : (U'.gen.inv ≫ (Over.pullback (jK R)).map pr) ≫ ((Over.pullback (jK R)).map inc ≫ U'.gen.hom) = oA.act F.e := by
    have e1 := hlin.ext F.e
    rw [← hpi, CategoryTheory.Functor.map_comp] at e1
    rw [Category.assoc, ← Category.assoc ((Over.pullback (jK R)).map pr), e1, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have h2 := GlobalTheory.T.rosati_star_mul_kills_point_of_trivial_pairing (FractionRing R) A' F.O oA F.e F.f ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).map inc ≫ U'.gen.hom) (U'.gen.inv ≫ (Over.pullback (jK R)).map pr) hra T (x ≫ (Over.pullback (jK R)).map inc ≫ U'.gen.hom) h1
  have hip' : (Over.pullback (jK R)).map inc ≫ (Over.pullback (jK R)).map pr = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, hip, CategoryTheory.Functor.map_id]
  have he : (x ≫ (Over.pullback (jK R)).map inc ≫ U'.gen.hom) ≫ oA.act F.e = x ≫ (Over.pullback (jK R)).map inc ≫ U'.gen.hom := by
    rw [← hra]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc ((Over.pullback (jK R)).map inc) ((Over.pullback (jK R)).map pr), hip', Category.id_comp]
  obtain ⟨-, hsym, g, hg⟩ := hF
  set y := x ≫ (Over.pullback (jK R)).map inc ≫ U'.gen.hom with hy
  have hu : y ≫ oA.act (Star.star F.e * F.f * F.e) = toUnit T ≫ η[A'.A] := by
    rw [hsym, oA.map_mul, ← Category.assoc, he, h2]
  have h3 : y = toUnit T ≫ η[A'.A] := by
    have : IsMonHom (oA.act g) := oA.hom g
    rw [← he, ← hg, oA.map_mul, ← Category.assoc, hu, Category.assoc, IsMonHom.one_hom]
  have hx' : x = y ≫ U'.gen.inv ≫ (Over.pullback (jK R)).map pr := by
    rw [hy]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [hip', Category.comp_id]
  rw [hx', h3]
  have hη : η[A'.A] ≫ U'.gen.inv = η[(Over.pullback (jK R)).obj G'] := by
    have : IsMonHom U'.gen.hom := U'.gen_hom
    rw [← IsMonHom.one_hom U'.gen.hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have : IsMonHom ((Over.pullback (jK R)).map pr) := inferInstance
  rw [Category.assoc, ← Category.assoc η[A'.A], hη, IsMonHom.one_hom]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialSumCompMonHomEqPartialSum
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProd.PsumMap

theorem psum_comp_hom : ∀ (S : Scheme.{0}) (B B₁ T : Over S) [GrpObj B] [IsCommMonObj B] [GrpObj B₁] [IsCommMonObj B₁] (n : ℕ) (p : B ⟶ B₁) (x : Fin n → (T ⟶ B)) (x₁ : Fin n → (T ⟶ B₁)), IsMonHom p → (∀ i, x i ≫ p = x₁ i) → ∀ I : Finset (Fin n), psum B x I ≫ p = psum B₁ x₁ I := by
  intro S B B₁ T _ _ _ _ n p x x₁ hp hx I
  unfold psum
  induction ((List.finRange n).filter (· ∈ I)) with
  | nil =>
    show (toUnit T ≫ η[B]) ≫ p = toUnit T ≫ η[B₁]
    rw [Category.assoc, IsMonHom.one_hom]
  | cons a l ih =>
    rw [List.foldr_cons, List.foldr_cons, ← ih]
    show (lift (x a) _ ≫ μ[B]) ≫ p = lift (x₁ a) _ ≫ μ[B₁]
    rw [Category.assoc, IsMonHom.mul_hom, ← Category.assoc, lift_map, hx a]

end GlobalTheory.MumProd.PsumMap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicardClassEqZeroAffineMilnorSquareStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.picardClass_eq_zero_affineMilnorSquare : ∀ (S : Scheme.{0}) (A T T₁ T₂ T₀ : Over S) [Flat A.hom] (j₁ : T₁ ⟶ T) (j₂ : T₂ ⟶ T) (k₁ : T₀ ⟶ T₁) (k₂ : T₀ ⟶ T₂), Milnor j₁.left j₂.left k₁.left k₂.left → Function.Surjective (Units.map (A ◁ k₂).left.appTop.hom.toMonoidHom) → ∀ c : Pic (A ⊗ T).left, GlobalTheory.CechPic.pull (A ◁ j₁).left c = 0 → GlobalTheory.CechPic.pull (A ◁ j₂).left c = 0 → c = 0 := by
  first | exact @GlobalTheory.DualOpen.pic_eq_zero_of_milnor | exact GlobalTheory.DualOpen.pic_eq_zero_of_milnor | (intros; apply GlobalTheory.DualOpen.pic_eq_zero_of_milnor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationFormRingActionSymmetricStatement
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarization_form_ring_action_symmetric : GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}
    {R : Type} [CommRing R] (X : Obj F 𝔠 (Sp R)) (c : 𝔠.elt) (ψ : LinearMap.BilinForm R (HdR X.A)),
    IsPolForm (dp0 R) (𝟙 _) X.A (X.diag c) ψ → ∀ (b : 𝓞 F) (x y : HdR X.A),
      ψ (act (dp0 R) (𝟙 _) X.rm b x) y = ψ x (act (dp0 R) (𝟙 _) X.rm b y) := by
  first | exact @GlobalTheory.RealMultAdjoint.polForm_adjoint_rm | exact GlobalTheory.RealMultAdjoint.polForm_adjoint_rm | (intros; apply GlobalTheory.RealMultAdjoint.polForm_adjoint_rm <;> assumption)
end

