import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2355
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0074
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0616
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1565
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1671
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2328
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1713
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1727
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0185
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1782
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1847
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2341
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2327
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1882
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1877
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1879
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0623
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2344

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatGaugeCoverOpenLeHeatOperatorOpen
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT pbT)
open GlobalTheory.LogKS (IsField)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat.Gauge

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {n : ℕ} {X : Scheme.{0}}
  (m : G.left ⟶ X) {m₁ : G.left ⟶ X} {L : LB X} {dd : Fin n → Fld G.left} {D : R → R} (h₁ : Heat G m₁ L dd D)

def W (p : h₁.J × (Fin 2 → L.ι)) : G.left.Opens := h₁.W p.1 ⊓ LB.wchart L ![m, m₁] p.2

theorem heatGaugeCoverOpen_le_heatOperatorOpen (p : h₁.J × (Fin 2 → L.ι)) : W m h₁ p ≤ h₁.W p.1 := inf_le_left

theorem W_le_wchart (p : h₁.J × (Fin 2 → L.ι)) : W m h₁ p ≤ LB.wchart L ![m, m₁] p.2 := inf_le_right

theorem W_le_m (p : h₁.J × (Fin 2 → L.ι)) : W m h₁ p ≤ m ⁻¹ᵁ L.U (p.2 0) :=
  (W_le_wchart m h₁ p).trans (LB.wchart_le L ![m, m₁] p.2 0)

theorem W_le_m₁ (p : h₁.J × (Fin 2 → L.ι)) : W m h₁ p ≤ m₁ ⁻¹ᵁ (L.U (p.2 1) ⊓ L.U (h₁.j p.1)) :=
  fun _ hy => ⟨LB.wchart_le L ![m, m₁] p.2 1 hy.2, h₁.le p.1 hy.1⟩

variable (e : LB.Gen (LB.LinComb L ![m, m₁] ![1, -1]))

def gU (p : h₁.J × (Fin 2 → L.ι)) : Γ(G.left, W m h₁ p)ˣ :=
  res (W_le_wchart m h₁ p) (e.s p.2) * res (W_le_m₁ m h₁ p) (pullU m₁ _ (L.g (p.2 1) (h₁.j p.1)))

def gL (a : Fin n) (p : h₁.J × (Fin 2 → L.ι)) : Γ(G.left, W m h₁ p) :=
  dd a (W m h₁ p) (gU m h₁ e p).val * (gU m h₁ e p)⁻¹.val

def gE (p : h₁.J × (Fin 2 → L.ι)) : Γ(G.left, W m h₁ p) :=
  h₁.d p.1 (W m h₁ p) (gU m h₁ e p).val * (gU m h₁ e p)⁻¹.val

def gY (a : Fin n) (p : h₁.J × (Fin 2 → L.ι)) : Γ(G.left, W m h₁ p) :=
  ∑ b, constFn G.hom (W m h₁ p) (h₁.Θ a b) * gL m h₁ e b p

def gD (p : h₁.J × (Fin 2 → L.ι)) : Fld G.left :=
  fun O f => h₁.d p.1 O f + ∑ a, rsT (gY m h₁ e a p) O * dd a O f

def gP (c : R) (p : h₁.J × (Fin 2 → L.ι)) : Γ(G.left, W m h₁ p) :=
  rsT (h₁.p p.1) (W m h₁ p) - gE m h₁ e p -
    constFn G.hom (W m h₁ p) c * ∑ a, ∑ b, constFn G.hom (W m h₁ p) (h₁.Θ a b) * gL m h₁ e a p * gL m h₁ e b p

def gP' (c : R) (p : h₁.J × (Fin 2 → L.ι)) : Γ(G.left, W m h₁ p) :=
  rsT (h₁.p' p.1) (W m h₁ p) +
    constFn G.hom (W m h₁ p) c * ∑ a, ∑ b, constFn G.hom (W m h₁ p) (h₁.Θ a b) * dd a (W m h₁ p) (gL m h₁ e b p) -
    ∑ a, constFn G.hom (W m h₁ p) (h₁.u a) * gL m h₁ e a p

theorem isField_mono {Z : Scheme.{0}} {W₀ W₁ : Z.Opens} {d : Fld Z} (h : IsField W₀ d) (hle : W₁ ≤ W₀) :
    IsField W₁ d :=
  ⟨fun W hW => h.1 W (hW.trans hle), fun W hW => h.2.1 W (hW.trans hle),
    fun W W' hWW' hW => h.2.2 W W' hWW' (hW.trans hle)⟩

open GlobalTheory.KS in

theorem op_rsT {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {n : ℕ}
    (dd : Fin n → Fld G.left) (hdd : ∀ a, IsField ⊤ (dd a)) (Θ : Matrix (Fin n) (Fin n) R) (u : Fin n → R)
    (d : Fld G.left) {W₀ : G.left.Opens} (p p' : Γ(G.left, W₀)) (k : ℕ) {O O' : G.left.Opens}
    (hd : IsField O d) (hO : O ≤ W₀) (h : O' ≤ O) (f : Γ(G.left, O)) :
    rsT (op G dd Θ u d p p' k O f) O' = op G dd Θ u d p p' k O' (rsT f O') := by
  have hd' : ∀ g, resG G.left h (d O g) = d O' (resG G.left h g) :=
    fun g => (hd.2.2 O O' h le_rfl g).symm
  have hdd' : ∀ a g, resG G.left h (dd a O g) = dd a O' (resG G.left h g) :=
    fun a g => ((hdd a).2.2 O O' h le_top g).symm
  have hc : ∀ r, resG G.left h (constFn G.hom O r) = constFn G.hom O' r :=
    fun r => (rsT_of_le h _).symm.trans (rsT_constFn G.hom h r)
  have hp : ∀ q : Γ(G.left, W₀), resG G.left h (rsT q O) = rsT q O' := fun q => by
    rw [← rsT_of_le h, rsT_rsT hO h]
  rw [rsT_of_le h, rsT_of_le h]
  simp only [op, map_add, map_sub, map_mul, map_sum, map_pow, map_natCast, map_ofNat, hd', hdd', hc, hp]

theorem trans_factor {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {O : Type} [CommRing O] [StarRing O]
    [Module O Q.X] (oa : Q.OAct O) (Y : GlobalTheory.RayEv.Ray oa) (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) :
    ∃ τ : Q.P.A.left ⟶ Q.P.A.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left = Y.q.left ≫ τ := by
  haveI : IsMonHom Y.q := Y.q_linear.isMonHom
  refine ⟨(𝟙 Q.P.A * (toUnit Q.P.A ≫ x ≫ Y.q)).left, ?_⟩
  have e : (𝟙 Y.H * (toUnit Y.H ≫ x)) ≫ Y.q = Y.q ≫ (𝟙 Q.P.A * (toUnit Q.P.A ≫ x ≫ Y.q)) := by
    rw [MonObj.mul_comp, MonObj.comp_mul, Category.id_comp, Category.comp_id, ← Category.assoc Y.q (toUnit _),
      toUnit_unique (Y.q ≫ toUnit Q.P.A) (toUnit Y.H), Category.assoc]
  exact congrArg (fun f => f.left) e

end GlobalTheory.Heat.Gauge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairWithSectionsRepresentsTensor
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VolBr.Pair

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem loc_one_add (P : Pair p) (a b a' b' : ℤ) (i : P.L.B.ι) (j : P.A.B.ι) :
    P.loc (a + a') (b + b') 1 i j = P.loc a b 1 i j * P.loc a' b' 1 i j := by
  have h₁ : ((P.r i : X.functionFieldˣ) : X.functionField) ≠ 0 := (P.r i).ne_zero
  have h₂ : ((P.r' j : X.functionFieldˣ) : X.functionField) ≠ 0 := (P.r' j).ne_zero
  simp only [loc, one_mul, zpow_add₀ h₁, zpow_add₀ h₂]
  ring

theorem rep_tens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p),
    ∀ (a b a' b' : ℤ) (M M' : HermLB p), P.Rep a b M → P.Rep a' b' M' →
      P.Rep (a + a') (b + b') (M.tens M') := by
  intro k _ X _ p P a b a' b' M M' ⟨ρ, hρ, hu, hn⟩ ⟨ρ', hρ', hu', hn'⟩
  have e (c : (M.tens M').B.ι) (i : P.L.B.ι) (j : P.A.B.ι) :
      (((ρ c.1 * ρ' c.2 : X.functionFieldˣ) : X.functionField) / P.loc (a + a') (b + b') 1 i j) =
        ((ρ c.1 : X.functionField) / P.loc a b 1 i j) * ((ρ' c.2 : X.functionField) / P.loc a' b' 1 i j) := by
    rw [loc_one_add, Units.val_mul]
    ring
  refine ⟨fun c => ρ c.1 * ρ' c.2, GlobalTheory.PtHtComb.isRatSec_tens hρ hρ', ?_, ?_⟩
  · intro x c i j hc hi hj
    rw [e]
    exact (hu x c.1 i j hc.1 hi hj).mul (hu' x c.2 i j hc.2 hi hj)
  · intro σ y c i j hc hi hj
    obtain ⟨hc₁, hc₂⟩ := mem_ptsIn_inf.1 hc
    have u₁ := hu _ c.1 i j (mem_ptsIn.1 hc₁) (mem_ptsIn.1 hi) (mem_ptsIn.1 hj)
    have u₂ := hu' _ c.2 i j (mem_ptsIn.1 hc₂) (mem_ptsIn.1 hi) (mem_ptsIn.1 hj)
    have n₁ := hn σ y c.1 i j hc₁ hi hj
    have n₂ := hn' σ y c.2 i j hc₂ hi hj
    have z₁ : ‖ratVal ((ρ c.1 : X.functionField) / P.loc a b 1 i j) y‖ ≠ 0 :=
      norm_ne_zero_iff.2 (ratVal_ne_zero u₁)
    have z₂ : ‖ratVal ((ρ' c.2 : X.functionField) / P.loc a' b' 1 i j) y‖ ≠ 0 :=
      norm_ne_zero_iff.2 (ratVal_ne_zero u₂)
    change Real.log ‖ratVal ((((ρ c.1 * ρ' c.2 : X.functionFieldˣ) : X.functionField)) /
        P.loc (a + a') (b + b') 1 i j) y‖ - ((M.φ σ).φ c.1 y + (M'.φ σ).φ c.2 y) / 2 = _
    rw [e, ratVal_mul u₁.regAt u₂.regAt, norm_mul, Real.log_mul z₁ z₂]
    push_cast
    linear_combination n₁ + n₂

end GlobalTheory.VolBr.Pair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HessRelFnB
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts

namespace GlobalTheory.Mean4O

variable {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F}

def ConjInv (A : Adl C Y) : Prop :=
  ∀ (σ σ' : F →+* ℂ) (y : Pts Y σ) (y' : Pts Y σ'), y'.1 = spMap (starRingEnd ℂ) ≫ y.1 →
    C.pn Y σ' A.D (A.m σ') (C.cx Y σ' (genAt A.D (under y'))) y' =
      C.pn Y σ A.D (A.m σ) (C.cx Y σ (genAt A.D (under y))) y

namespace Cover

variable (V : Cover Y)

def FinInd (A : Adl C Y) (B : LB V.X) (r : (B.pull V.j).ι → V.G.functionFieldˣ) : Prop :=
  IsRatSec (B.pull V.j) r ∧
    (∀ i, ∀ x ∈ (B.pull V.j).U i, UnitAt x (V.φ (genAt A.D (V.π x)) * r i)) ∧
    ∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X)
      (i : (B.pull V.j).ι), z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ B.U (i PUnit.unit) →
      A.lg v e y = Real.log (e.w (valAt z (V.φ (genAt A.D (below y.1)) * (r i : V.G.functionField))))

end Cover

def HessRel {e : ℕ} {M : Man e} {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}
    (ε : (k →+* ℂ) → Fin (M.n + 1)) (π : ∀ σ, CxPts p σ → M.X (ε σ)) (L : HermLB p) (P : M.Pot) : Prop :=
  ∀ (σ : k →+* ℂ) (c : AlgChart p σ e), ∀ y ∈ c.e.source, ∀ i, y ∈ ptsIn p σ (L.B.U i) →
    c.hess (L.φ σ) i y =
      ReciprocityTheory.L2DbarEstimates.cHess e (fun v => ((2 * (P (ε σ)).φ (π σ y) (π σ (c.e.symm v)) : ℝ) : ℂ)) (c.e y)

theorem hessRel_fnB {e : ℕ} {M : Man e} {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}
    (ε : (k →+* ℂ) → Fin (M.n + 1)) (π : ∀ σ, CxPts p σ → M.X (ε σ)) (u : M.Fun) (hu hc) :
    HessRel ε π (ArInt.fnB (M.pull ε π ((2 : ℝ) • u)) hu hc) fun a => LocPot.ofFun (u a) :=
  fun _ _ _ _ _ _ => rfl

end GlobalTheory.Mean4O
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeDeRhamOnModificationOfFlagCover
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

namespace GlobalTheory.HorFrame

def combDer {R : Type} [CommRing R] {ι : Type} [Fintype ι] (δ : ι → (R →+* DualNumber R))
    (hδ : ∀ i s, (δ i s).fst = s) (A : ι → R) : R →+* DualNumber R where
  toFun s := TrivSqZeroExt.inl s + TrivSqZeroExt.inr (∑ i, A i * (δ i s).snd)
  map_one' := by
    have h : ∀ i, (δ i 1).snd = 0 := fun i => by rw [map_one]; rfl
    ext <;> simp [h]
  map_mul' x y := by
    have h : ∀ i, (δ i (x * y)).snd = x * (δ i y).snd + (δ i x).snd * y := fun i => by
      rw [map_mul, TrivSqZeroExt.snd_mul, hδ, hδ, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
        MulOpposite.unop_op]
    ext
    · simp
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add,
        TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero,
        smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, h, Finset.mul_sum, Finset.sum_mul,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
  map_zero' := by
    have h : ∀ i, (δ i 0).snd = 0 := fun i => by rw [map_zero]; rfl
    ext <;> simp [h]
  map_add' x y := by
    ext <;> simp [Finset.sum_add_distrib, mul_add]

theorem combDer_fst {R : Type} [CommRing R] {ι : Type} [Fintype ι] (δ : ι → (R →+* DualNumber R))
    (hδ : ∀ i s, (δ i s).fst = s) (A : ι → R) (s : R) : (combDer δ hδ A s).fst = s := by
  simp [combDer]

theorem combDer_snd {R : Type} [CommRing R] {ι : Type} [Fintype ι] (δ : ι → (R →+* DualNumber R))
    (hδ : ∀ i s, (δ i s).fst = s) (A : ι → R) (s : R) :
    (combDer δ hδ A s).snd = ∑ i, A i * (δ i s).snd := by
  simp [combDer]

theorem fst_dualMap {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (x : DualNumber S) :
    (dualMap φ x).fst = φ x.fst := by simp [dualMap]

theorem snd_dualMap {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (x : DualNumber S) :
    (dualMap φ x).snd = φ x.snd := by simp [dualMap]

end GlobalTheory.HorFrame

open GlobalTheory.HorFrame in

theorem GlobalTheory.HorFrame.exists_horizontal_lift : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) (hP : GlobalTheory.Published.AbelianDeRham)
    (hKS : ∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y) (k : X.F.J)
    (W : M.X.Opens) (hW : W ≤ M.off ⊓ (toFlag M) ⁻¹ᵁ X.F.U k) (p : M.X) (hp : p ∈ W), ∃ (W' : M.X.Opens) (hW' : IsAffineOpen W')
      (e : HIx Dw (psiSet H) → (Γ(M.X, W') →+* DualNumber Γ(M.X, W'))),
      p ∈ W' ∧ W' ≤ W ∧ (∀ b s, (e b s).fst = s) ∧
      ∀ (K : Type) [Field K] [Algebra c.F K] (ψ : Γ(M.X, W') →+* K)
        (hk : ⊤ ≤ ((spMap ψ ≫ tau hW') ≫ toFlag M) ⁻¹ᵁ X.F.U k) (Q : FrPt Xo c K),
        X.F.ChartFr k _ hk Q → ∀ b, ∃ w : FrPt Xo c (DualNumber K), IsDef Q w ∧
          GlobalTheory.FlagTan.IsKS (psiSet H) Q w.x (Pi.single b 1) ∧
          spMap ((dualMap ψ).comp (e b)) ≫ tau hW' ≫ toFlag M = X.ptY w := by
  intro E _ _ _ H Dw l Xo c Y X Z M hP hKS k W hW p hp
  haveI := c.fin
  obtain ⟨W₁, hW₁, d, hpW₁, hW₁W, hd, hspan⟩ := GlobalTheory.T.exists_affine_cover_with_dual_number_derivations M W p hp
  have hoff : W₁ ≤ M.off := fun x hx => (hW (hW₁W hx)).1
  have hτ : ⊤ ≤ tau hW₁ ⁻¹ᵁ W₁ := tau_le hW₁ le_rfl
  have hk₁ : ⊤ ≤ (tau hW₁ ≫ toFlag M) ⁻¹ᵁ X.F.U k := fun s _ => (hW (hW₁W (hτ (Set.mem_univ s)))).2
  have hF₁ : ⊤ ≤ (tau hW₁ ≫ toFlag M) ⁻¹ᵁ flagOpen X := fun s _ => by
    have := hoff (hτ (Set.mem_univ s))
    rw [M.off_eq] at this
    exact this
  obtain ⟨alg₁, hch⟩ := GlobalTheory.CompHS.exists_chartFr (tau hW₁ ≫ toFlag M) hF₁
  obtain ⟨Q₀, hQ₀⟩ := hch k hk₁
  have hdalg : ∀ b, (d b).comp (algebraMap c.F Γ(M.X, W₁)) = algebraMap c.F (DualNumber Γ(M.X, W₁)) :=
    fun b => RingHom.ext fun a => TrivSqZeroExt.ext
      (by rw [RingHom.comp_apply, hd]; rfl) (by
      rw [GlobalTheory.T.ringHom_numberField_dualNumber_snd_eq_zero c.F ((d b).comp (algebraMap c.F _)) a]; rfl)
  have hx1 : ∀ b, (spMap (d b) ≫ Q₀.x) ≫ Xo.s = sOf c (DualNumber Γ(M.X, W₁)) := fun b => by
    rw [Category.assoc, Q₀.x_over]
    unfold sOf
    rw [spMap_comp', ← RingHom.comp_assoc, hdalg]
  have hx2 : ∀ b, spMap (TrivSqZeroExt.fstHom Γ(M.X, W₁) Γ(M.X, W₁) Γ(M.X, W₁)).toRingHom ≫ spMap (d b) ≫ Q₀.x
      = Q₀.x := fun b => by
    rw [← Category.assoc, spMap_comp']
    have : (TrivSqZeroExt.fstHom Γ(M.X, W₁) Γ(M.X, W₁) Γ(M.X, W₁)).toRingHom.comp (d b) = RingHom.id _ :=
      RingHom.ext fun s => hd b s
    rw [this]
    exact (congrArg (· ≫ Q₀.x) (Spec.map_id _)).trans (Category.id_comp _)
  choose Mx hMx using fun b => GlobalTheory.T.exists_kodairaSpencerMatrix_firstOrderDeformation hP Q₀ (spMap (d b) ≫ Q₀.x) (hx1 b) (hx2 b)
  obtain ⟨B, hB⟩ := GlobalTheory.T.exists_basicOpen_kodairaSpencer_left_inverse M hKS k hW₁ hoff hk₁ Q₀ hQ₀ d hd hspan Mx hMx p hpW₁
  set MxM : Matrix (Fin (dimFlag Dw)) (HIx Dw (psiSet H)) Γ(M.X, W₁) := Matrix.of (fun a h => Mx a h) with hMxM
  set g : Γ(M.X, W₁) := (B * MxM).det with hg
  have hW' : IsAffineOpen (M.X.basicOpen g) := hW₁.basicOpen g
  have hW'W₁ : M.X.basicOpen g ≤ W₁ := M.X.basicOpen_le g
  haveI := hW₁.isLocalization_basicOpen g
  set ρ := algebraMap Γ(M.X, W₁) Γ(M.X, M.X.basicOpen g) with hρ
  choose d' hd'1 hd'2 using fun b => GlobalTheory.T.exists_dualNumber_deformation_extend_away (S' := Γ(M.X, M.X.basicOpen g)) g (d b) (hd b)
  have hunit : IsUnit ((B * MxM).map ρ).det := by
    have : ((B * MxM).map ρ).det = ρ (B * MxM).det := by rw [RingHom.map_det]; rfl
    rw [this]
    exact IsLocalization.Away.algebraMap_isUnit g
  set A := ((B * MxM).map ρ)⁻¹ * B.map ρ with hA
  have hAM : A * MxM.map ρ = 1 := by
    rw [hA, Matrix.mul_assoc, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hunit]
  have hτ' : spMap ρ ≫ tau hW₁ = tau hW' := by
    have e1 := spMap_ev (tau hW') hW₁ (tau_le hW' hW'W₁)
    have e2 : ev (tau hW') W₁ (tau_le hW' hW'W₁) = ρ := RingHom.ext fun a => ev_tau hW' hW'W₁ _ a
    rw [← e2]
    exact e1
  refine ⟨M.X.basicOpen g, hW', fun b => combDer d' hd'1 (fun a => A b a), hB, hW'W₁.trans hW₁W,
    fun b s => combDer_fst _ _ _ _, ?_⟩
  intro K _ _ ψ hk Q hQ b
  have ez : (spMap ψ ≫ tau hW') ≫ toFlag M = (spMap (ψ.comp ρ) ≫ tau hW₁) ≫ toFlag M := by
    rw [← hτ', ← spMap_comp' ρ ψ]
    simp only [Category.assoc]
  have hk' : ⊤ ≤ ((spMap (ψ.comp ρ) ≫ tau hW₁) ≫ toFlag M) ⁻¹ᵁ X.F.U k := ez ▸ hk
  have hQ' : X.F.ChartFr k _ hk' Q :=
    hQ.frMap (frMap_refl Q) ((spMap_algId _).trans ez) hk'
  obtain ⟨w, hwD, hwKS, hwpt⟩ := GlobalTheory.T.exists_chart_frame_deformation_of_derivation_combination M hKS k hW₁ hk₁ Q₀ hQ₀ d hd Mx hMx K (ψ.comp ρ) hk' Q hQ'
    ((dualMap ψ).comp ((combDer d' hd'1 (fun a => A b a)).comp ρ)) (fun a => ψ (A b a))
    (fun s => by rw [RingHom.comp_apply, fst_dualMap, RingHom.comp_apply, combDer_fst]; rfl)
    (fun s => by
      rw [RingHom.comp_apply, snd_dualMap, RingHom.comp_apply, combDer_snd, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_mul, hd'2]
      rfl)
  refine ⟨w, hwD, ?_, ?_⟩
  · have key : ∀ h, ∑ a, ψ (A b a) * ψ (ρ (Mx a h)) = (Pi.single b (1 : K) : HIx Dw (psiSet H) → K) h := fun h => by
      have e := congrArg (fun N => ψ (N b h)) hAM
      simp only [Matrix.mul_apply, Matrix.map_apply, hMxM, Matrix.of_apply, map_sum, map_mul] at e
      rw [e, Matrix.one_apply, Pi.single_apply]
      by_cases hh : h = b
      · subst hh; simp
      · simp [hh, Ne.symm hh]
    convert hwKS using 1
    funext h
    rw [Finset.sum_apply, ← key h]
    rfl
  · rw [← hwpt, ← hτ']
    simp only [← Category.assoc, spMap_comp']
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateShiftCmStatement
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_shift_cm : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.FlatCM.PlaceShiftSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), HTShift Xo c := by
  first | exact @GlobalTheory.HTShiftPf.htShift | exact GlobalTheory.HTShiftPf.htShift | (intros; apply GlobalTheory.HTShiftPf.htShift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperCohomologyRestrictAdjointBijective
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AdjHyp

def counitCoef {R : Type} [CommRing R] {C C' : Type} [Category.{0} C] [Category.{0} C']
    (F : C ⥤ CommAlgCat.{0} R) {G : C' ⥤ C} {H : C ⥤ C'} (adj : G ⊣ H) :
    CoefMap (RingHom.id R) (G ⋙ F) F where
  G := H
  α V := (mp F (adj.counit.app V)).toRingHom
  naturality {V V'} φ b := by
    change mp F (adj.counit.app V') (mp F (G.map (H.map φ)) b) = mp F φ (mp F (adj.counit.app V) b)
    rw [← mp_comp, ← mp_comp]
    have e := adj.counit.naturality φ
    simp only [Functor.comp_map, Functor.id_map] at e
    rw [e]
  smul V r b := by
    change mp F (adj.counit.app V) (r • b) = r • mp F (adj.counit.app V) b
    exact map_smul _ r b

theorem main : ∀ (R : Type) [CommRing R] (C C' : Type) [Category.{0} C] [Category.{0} C']
    (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) (H : C ⥤ C'), (G ⊣ H) →
    Function.Bijective (pullHyp1 (CoefMap.restrict F G)) := by
  intro R _ C C' _ _ F G H adj
  have hl : ∀ c, pullHyp1 (counitCoef F adj) (pullHyp1 (CoefMap.restrict F G) c) = c := by
    intro c
    rw [← pullHyp1_comp]
    exact (pullHyp1_eq_of_natTrans _ (CoefMap.id F) adj.counit (fun T b ↦ rfl) c).trans
      (pullHyp1_id c)
  have hr : ∀ c, pullHyp1 (CoefMap.restrict F G) (pullHyp1 (counitCoef F adj) c) = c := by
    intro c
    rw [← pullHyp1_comp]
    refine ((pullHyp1_eq_of_natTrans (CoefMap.id (G ⋙ F))
      ((counitCoef F adj).comp (CoefMap.restrict F G)) adj.unit (fun T b ↦ ?_) c).symm.trans
      (pullHyp1_id c))
    change mp F (adj.counit.app (G.obj T)) (mp F (G.map (adj.unit.app T)) b) = b
    exact (mp_comp F (G.map (adj.unit.app T)) (adj.counit.app (G.obj T)) b).symm.trans
      ((congrArg (fun ξ ↦ mp F ξ b) (adj.left_triangle_components T)).trans (mp_id F (G.obj T) b))
  exact ⟨Function.LeftInverse.injective hl, Function.RightInverse.surjective hr⟩

end GlobalTheory.AdjHyp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneSplitSelfDualHermitianComplement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PlaneComplement

theorem plane_split_complement : ∀ (D : D7) (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (q : ℕ),
    IsSelfDualC S Λ → NegIdx S (q + 1) → q + 2 ≤ S.rank → 3 ≤ S.rank →
    ∃ (S₁ : HSp D) (Λ₁ : Submodule (𝓞 D.host.E) (Fin S₁.rank → D.host.E)) (ι : S₁.V →ₗ[D.host.E] S.V) (x y : S.V),
      GlobalTheory.SqStepK.PlaneSplit S S₁ Λ Λ₁ ι x y ∧ S₁.SigOK ∧ IsSelfDualC S₁ Λ₁ ∧ NegIdx S₁ q := by
  intro D S Λ q hΛ hneg hq h3
  obtain ⟨x, hx0, hxx⟩ := GlobalTheory.T.exists_isotropic_hermitianSpace_of_negativeIndex D S (q + 1) hneg (by omega) (by omega) h3
  obtain ⟨y, hyy, hxy, hsp⟩ := GlobalTheory.T.exists_hyperbolicPartner_splitting_selfDualLattice D S Λ x hΛ hx0 hxx
  obtain ⟨S₁, Λ₁, ι, hPS, hSD, hs⟩ := GlobalTheory.T.exists_selfDual_orthogonalComplement_hyperbolicPlane D S Λ x y (fun _ => (S.rank - 2 - q, q)) hΛ hxx hyy hxy hsp
  have hrk : S.rank = S₁.rank + 2 := hPS.1
  have hsig := GlobalTheory.T.hyperbolicPlaneComplement_negativeIndex_pred D S S₁ ι x y q hrk hPS.2.1 hxx hyy hxy
    (fun u => ⟨(hPS.2.2.2.2.2.1 u).1, (hPS.2.2.2.2.2.1 u).2⟩) hneg
  have e : S.rank - 2 - q = S₁.rank - q := by omega
  refine ⟨S₁, Λ₁, ι, x, y, hPS, fun τ => ?_, hSD, fun τ => ?_⟩
  · rw [hs]; simp only [e]; exact hsig τ
  · exact hsig _

end GlobalTheory.PlaneComplement

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealAlongLocalSpecVanishingIdealComplEqSpan
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PolDeg

theorem idlAlong_vanishingIdeal_compl (S : Scheme.{0}) (U : S.Opens) (R : Type) [CommRing R] [IsLocalRing R]
    (ξ : Sp R ⟶ S) (f : R) (hf : (Ideal.span {f}).IsRadical) (hU : ∀ p : Sp R, ξ p ∈ (U : Set S) ↔ f ∉ p.asIdeal)
    (hrad : ∀ I : Ideal (S.presheaf.stalk (ξ (closedPoint R))), I.IsRadical →
      (I.map (Scheme.stalkClosedPointTo ξ).hom).IsRadical) :
    idlAlong (Scheme.IdealSheafData.vanishingIdeal U.compl) ξ = Ideal.span {f} := by
  have hs := GlobalTheory.VanStalk.van_spec U.compl (ξ (closedPoint R))
  refine GlobalTheory.VanStalk.eq_of_forall_prime (hrad _ hs.1) hf fun q => ?_
  rw [idlAlong, Ideal.map_le_iff_le_comap, Ideal.span_singleton_le_iff_mem]
  refine (hs.2 (PrimeSpectrum.comap (Scheme.stalkClosedPointTo ξ).hom q)).symm.trans ?_
  have e := congrArg (fun g => g q) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ)
  change (Spec.map (Scheme.stalkClosedPointTo ξ) ≫ S.fromSpecStalk (ξ (closedPoint R))) q ∈ (U.compl : Set S) ↔ _
  rw [e]
  change ξ q ∉ (U : Set S) ↔ _
  rw [hU q, not_not]

end GlobalTheory.PolDeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleComponentsClopenPartitionStatement
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_clopen_irreducible_partition_of_normal_proj : ∀ (n : ℕ) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)), IsProjOver z → GlobalTheory.IsNormalScheme Z → ∃ (ι : Type) (_ : Fintype ι) (W : ι → Set Z), (∀ c, IsClopen (W c)) ∧ (∀ c, IsIrreducible (W c)) ∧ ∀ x, ∃! c, x ∈ W c := by
  first | exact @GlobalTheory.irreducibleComponents_clopen_partition | exact GlobalTheory.irreducibleComponents_clopen_partition | (intros; apply GlobalTheory.irreducibleComponents_clopen_partition <;> assumption)
end

