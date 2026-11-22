import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2267
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0652
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0112
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0653
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsAbelianSchemeOfAbelianThickenings
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0014

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointHeightDualAndLinearComb
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O
open GlobalTheory.CxPts Topology Set

namespace GlobalTheory.PtHtComb

variable {k : Type} [CommRing k] {Z : Scheme.{0}} [IsIntegral Z] {q : Z ⟶ Sp k}

theorem isRatSec_tens {A B : LB Z} {r : A.ι → Z.functionFieldˣ} {s : B.ι → Z.functionFieldˣ}
    (hr : IsRatSec A r) (hs : IsRatSec B s) :
    IsRatSec (CechPic.tens A B) fun c : A.ι × B.ι => r c.1 * s c.2 := fun (c c' : A.ι × B.ι) h => by
  have h₁ : genericPoint Z ∈ A.U c.1 ⊓ A.U c'.1 := ⟨h.1.1, h.2.1⟩
  have h₂ : genericPoint Z ∈ B.U c.2 ⊓ B.U c'.2 := ⟨h.1.2, h.2.2⟩
  have e : fnOf _ h ((CechPic.tens A B).g c c' : Γ(Z, _)) =
      fnOf _ h₁ (A.g c.1 c'.1 : Γ(Z, _)) * fnOf _ h₂ (B.g c.2 c'.2 : Γ(Z, _)) := by
    change fnOf _ h ((res _ (A.g c.1 c'.1)).val * (res _ (B.g c.2 c'.2)).val) = _
    exact (map_mul (fnOf _ h) _ _).trans (congrArg₂ (· * ·) (fnOf_resG _ h _) (fnOf_resG _ h _))
  rw [Units.val_mul, Units.val_mul, hr c.1 c'.1 h₁, hs c.2 c'.2 h₂, e]
  ring

theorem div_tens (M N : HermLB q) {r : M.B.ι → Z.functionFieldˣ} {s : N.B.ι → Z.functionFieldˣ}
    (hr : IsRatSec M.B r) (hs : IsRatSec N.B s) :
    (M.tens N).div (isRatSec_tens hr hs) = M.div hr + N.div hs :=
  CartierDiv.ext_of_isEqn fun z => by
    obtain ⟨a, ha⟩ := exists_chart M.isLB z
    obtain ⟨b, hb⟩ := exists_chart N.isLB z
    exact ⟨_, (presents_divOfRatSec (M.tens N).isLB (isRatSec_tens hr hs)).isEqn (a, b) z ⟨ha, hb⟩,
      ((presents_divOfRatSec M.isLB hr).isEqn a z ha).add ((presents_divOfRatSec N.isLB hs).isEqn b z hb)⟩

end GlobalTheory.PtHtComb

namespace GlobalTheory.PtHtComb

variable {k : Type} [CommRing k] {Z : Scheme.{0}} [IsIntegral Z] {q : Z ⟶ Sp k}

theorem curveDeg_tens [IsLocallyNoetherian Z] (hZ : IsArithVar q 0)
    (hc : CharZero (Z.residueField (genericPoint Z))) (M N : HermLB q) {r : M.B.ι → Z.functionFieldˣ}
    {s : N.B.ι → Z.functionFieldˣ} (hr : IsRatSec M.B r) (hs : IsRatSec N.B s) :
    (M.tens N).curveDeg (isRatSec_tens hr hs) = M.curveDeg hr + N.curveDeg hs := by
  have := hZ.isNoetherian
  have hfin (D : CartierDiv Z) : (Function.support fun z =>
      (D.mult z : ℝ) * Real.log (Nat.card (Z.residueField z))).Finite :=
    D.finite_support_mult.subset fun z hz h0 => hz (by simp [h0])
  have h₂ (σ) (y : CxPts q σ) : logNorm ((M.tens N).φ σ) (fun c : M.B.ι × N.B.ι => r c.1 * s c.2) y =
      logNorm (M.φ σ) r y + logNorm (N.φ σ) s y := by
    have hy : under y = genericPoint Z := hZ.under_eq_genericPoint y
    have ho (D : CartierDiv Z) : y ∈ offSupp q σ D := mem_offSupp.2 (hy ▸ D.genericPoint_notMem_supp)
    have ha := mem_pick (M.φ σ).isLB y
    have hb := mem_pick (N.φ σ).isLB y
    have hu (g : Z.functionFieldˣ) : ‖ratVal (g : Z.functionField) y‖ ≠ 0 :=
      norm_ne_zero_iff.2 (ratVal_ne_zero (hy ▸ unitAt_genericPoint g.ne_zero))
    refine (logNorm_eq ((M.tens N).φ σ) (isRatSec_tens hr hs) (ho _) (i := (pick (M.φ σ).isLB y, pick (N.φ σ).isLB y))
      (mem_ptsIn_inf.2 ⟨ha, hb⟩)).trans ?_
    change Real.log ‖ratVal ((r (pick (M.φ σ).isLB y) * s (pick (N.φ σ).isLB y) : Z.functionFieldˣ) : Z.functionField) y‖ -
      ((M.φ σ).φ (pick (M.φ σ).isLB y) y + (N.φ σ).φ (pick (N.φ σ).isLB y) y) / 2 = _
    rw [logNorm, logNorm, Units.val_mul,
      ratVal_mul (hy ▸ regAt_genericPoint _) (hy ▸ regAt_genericPoint _), norm_mul, Real.log_mul (hu _) (hu _)]
    ring
  have := SmallSecHeight.numberField hZ hc
  have : Finite (Σ σ : k →+* ℂ, CxPts q σ) := .of_equiv _ (SmallSecHeight.ptsEquiv hZ).symm
  have (σ : k →+* ℂ) : Finite (CxPts q σ) := .of_injective _ (sigma_mk_injective (i := σ))
  have := hZ.finite_emb
  have := Fintype.ofFinite (k →+* ℂ)
  have (σ : k →+* ℂ) := Fintype.ofFinite (CxPts q σ)
  unfold HermLB.curveDeg
  rw [div_tens M N hr hs]
  simp only [CartierDiv.mult_add, Int.cast_add, add_mul]
  rw [finsum_add_distrib (hfin _) (hfin _)]
  simp only [finsum_eq_sum_of_fintype, h₂, Finset.sum_add_distrib]
  ring

end GlobalTheory.PtHtComb

namespace GlobalTheory.PtHtComb

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}

theorem height_tens (hX : IsArithVar p D) {L M : HermLB p} {h h' h'' : X → ℝ} (H : L.IsArithHeight h)
    (H' : M.IsArithHeight h') (H'' : (L.tens M).IsArithHeight h'') {x : X} (hx : IsAlgPt x) :
    h'' x = h x + h' x := by
  obtain ⟨hc, hd⟩ := hx
  obtain ⟨Z, i, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint x
  have := hX.isNoetherian_sub i
  have hr : range i = closure {i (genericPoint Z)} := by
    have h₁ := (genericPoint_spec Z).image i.continuous
    rw [image_univ, i.isClosedEmbedding.isClosed_range.closure_eq] at h₁
    exact h₁.def.symm
  rw [topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hr] at hd
  have hbij : Function.Bijective (i.residueFieldMap (genericPoint Z)).hom := by
    refine ⟨RingHom.injective _, fun u => ?_⟩
    obtain ⟨u, rfl⟩ := Z.residue_surjective _ u
    obtain ⟨u, rfl⟩ := i.stalkMap_surjective _ u
    exact ⟨X.residue _ u, ConcreteCategory.congr_hom (Scheme.residue_residueFieldMap i _) u⟩
  have hc' : CharZero (Z.residueField (genericPoint Z)) := (RingHom.charZero_iff hbij.1).1 hc
  have hcΓ : CharZero Γ(Z, ⊤) := (Z.Γevaluation (genericPoint Z)).hom.charZero
  have hZ : IsArithVar (i ≫ p) 0 := hX.of_isClosedImmersion i hcΓ hd
  obtain ⟨r, hr⟩ := exists_isRatSec (L.restr i).isLB
  obtain ⟨s, hs⟩ := exists_isRatSec (M.restr i).isLB
  obtain ⟨t, ht, h₁, h₂⟩ := (HermLB.isometric_pull_tens (L := L) (M := M) i rfl).symm.exists_isRatSec
    (isRatSec_tens hr hs)
  rw [H''.point Z i hcΓ hd t ht, H.point Z i hcΓ hd r hr, H'.point Z i hcΓ hd s hs,
    ← curveDeg_tens hZ hc' (L.restr i) (M.restr i) hr hs, HermLB.curveDeg, h₁]
  refine congrArg _ (finsum_congr fun σ => finsum_congr fun y => h₂ σ (mem_offSupp.2 ?_))
  rw [hZ.under_eq_genericPoint]
  exact CartierDiv.genericPoint_notMem_supp _

theorem isPtHt_dual_comb : GlobalTheory.Published.ArExists → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ x : X, IsAlgPt x →
    (∀ (L : HermLB p) (a : ℝ), IsPtHt L x a → IsPtHt L.dual x (-a)) ∧
    ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p) (a : ι → ℝ), (∀ i, IsPtHt (L i) x (a i)) →
      ∀ n : ι → ℤ, IsPtHt (ArInt.comb L n) x (∑ i, (n i : ℝ) * a i) := by
  intro HE k _ X _ p D hX x hx
  have hex (L : HermLB p) : ∃ h, L.IsArithHeight h := (HE k X p D hX).1 L
  let ht (L : HermLB p) : ℝ := (hex L).choose x
  have hht {L : HermLB p} {h : X → ℝ} (H : L.IsArithHeight h) : ht L = h x :=
    congrFun ((hex L).choose_spec.unique hX H) x
  have hiso {L M : HermLB p} (e : L.Isometric M) : ht L = ht M :=
    (hht (e.isArithHeight hX (hex L).choose_spec)).symm
  have hadd (L M : HermLB p) : ht (L.tens M) = ht L + ht M :=
    height_tens hX (hex L).choose_spec (hex M).choose_spec (hex _).choose_spec hx
  let F₀ : HermLB.IsomClass p → ℝ := Quotient.lift (s := HermLB.isometrySetoid p) ht fun L M e => hiso e
  let F : HermLB.IsomClass p →+ ℝ := AddMonoidHom.mk' F₀ (by
    rintro ⟨L⟩ ⟨M⟩
    exact hadd L M)
  have hF (L : HermLB p) : F L.icls = ht L := rfl
  have hpt (L : HermLB p) (a : ℝ) : IsPtHt L x a ↔ F L.icls = a * Nat.card (X.residueField x →+* ℂ) :=
    ⟨fun ⟨h, H, e⟩ => (hht H).trans e, fun e => ⟨_, (hex L).choose_spec, e⟩⟩
  refine ⟨fun L a h => ?_, fun ι _ L a h n => ?_⟩
  · rw [hpt] at h ⊢
    rw [HermLB.icls_dual, map_neg, h, neg_mul]
  · simp only [hpt] at h ⊢
    rw [ArInt.icls_comb, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, h, zsmul_eq_mul, mul_assoc]

end GlobalTheory.PtHtComb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectionStatementHolds
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LineNorm
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv actR)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FlatModel.Proj

theorem exists_dual {O κ : Type} [CommRing O] [Fintype κ] [DecidableEq κ] (b : Module.Basis κ ℤ O)
    (hd : Algebra.discr ℤ b ≠ 0) :
    ∃ c : κ → O, (∀ a k, a * c k = ∑ i, b.repr (a * b i) k • c i) ∧
      ∑ i, c i * b i = ((Algebra.discr ℤ b : ℤ) : O) := by
  set T := Algebra.traceMatrix ℤ b with hT
  have hd' : T.det ≠ 0 := hd
  have nd : ∀ x y : O, (∀ l, Algebra.trace ℤ O (x * b l) = Algebra.trace ℤ O (y * b l)) → x = y := by
    intro x y h
    rw [← sub_eq_zero]
    have h1 : Matrix.vecMul (b.repr (x - y)) T = 0 := by
      funext l
      have h2 : Algebra.trace ℤ O ((x - y) * b l) = 0 := by rw [sub_mul, map_sub, h, sub_self]
      rw [← b.sum_repr (x - y), Finset.sum_mul, map_sum] at h2
      simp only [smul_mul_assoc, map_smul, smul_eq_mul] at h2
      exact h2
    have h3 := Matrix.eq_zero_of_vecMul_eq_zero hd' h1
    apply b.repr.injective
    rw [map_zero]
    exact DFunLike.coe_injective h3
  let c : κ → O := fun i => ∑ j, T.adjugate i j • b j
  have hc : ∀ i k, Algebra.trace ℤ O (c i * b k) = if i = k then T.det else 0 := by
    intro i k
    have h1 := congrFun (congrFun (Matrix.adjugate_mul T) i) k
    simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, _root_.mul_one, mul_zero] at h1
    rw [← h1]
    simp only [c, Finset.sum_mul, map_sum, smul_mul_assoc, map_smul, smul_eq_mul]
    rfl
  have hc2 : ∀ i x, Algebra.trace ℤ O (c i * x) = T.det * b.repr x i := by
    intro i x
    conv_lhs => rw [← b.sum_repr x]
    simp only [Finset.mul_sum, map_sum, mul_smul_comm, map_smul, hc, smul_eq_mul, mul_ite, mul_zero]
    simp [mul_comm]
  refine ⟨c, fun a k => nd _ _ fun l => ?_, nd _ _ fun l => ?_⟩
  · rw [mul_comm a, _root_.mul_assoc, hc2]
    simp only [Finset.sum_mul, map_sum, smul_mul_assoc, map_smul, hc, smul_eq_mul, mul_ite, mul_zero]
    simp [mul_comm]
  · simp only [Finset.sum_mul, map_sum, _root_.mul_assoc, hc2]
    rw [← zsmul_eq_mul, map_smul, Algebra.trace_eq_matrix_trace b, smul_eq_mul, Matrix.trace, ← Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, mul_comm]

section Lin

variable {O S M κ : Type} [CommRing O] [CommRing S] [AddCommGroup M] [Module S M] [Fintype κ]
  (ρ : O →+* Module.End S M) (σ : O →+* S) (b : Module.Basis κ ℤ O) (c : κ → O)

theorem eig_proj (hc : ∀ a k, a * c k = ∑ i, b.repr (a * b i) k • c i) (a : O) (v : M) :
    ρ a (∑ i, σ (c i) • ρ (b i) v) = σ a • ∑ i, σ (c i) • ρ (b i) v := by
  have h1 : ∀ i, ρ a (ρ (b i) v) = ∑ k, b.repr (a * b i) k • ρ (b k) v := fun i => by
    rw [← Module.End.mul_apply, ← map_mul]
    conv_lhs => rw [← b.sum_repr (a * b i)]
    simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply]
  simp only [map_sum, map_smul, h1, Finset.smul_sum, smul_smul, ← map_mul, hc, map_zsmul, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  rw [smul_comm, smul_assoc]

theorem proj_eig {d : ℤ} (hc : ∑ i, c i * b i = (d : O)) (v : M) (hv : ∀ a, ρ a v = σ a • v) :
    ∑ i, σ (c i) • ρ (b i) v = (d : S) • v := by
  simp only [hv, smul_smul, ← map_mul, ← Finset.sum_smul, ← map_sum, hc, map_intCast]

end Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X}

theorem eq_of_comb {S : Type} [CommRing S] {x : Sp S ⟶ X} {m : ℕ} (T : Fin m → TanM x t.G) {w : Fin m → S}
    {u : Sp (DualNumber S) ⟶ t.G.left} (h : IsCombAtG t x (fun i => (tv (T i)).left) w u) :
    u = (tv (∑ i, w i • T i)).left := by
  obtain ⟨y, hy, rfl⟩ := h
  obtain ⟨z, hz, e⟩ := (GlobalTheory.LieMet.isComb_iff T w _).2 rfl
  rw [← e]
  have : y = z := funext fun i => Over.OverMorphism.ext ((hy i).trans (hz i).symm)
  rw [this]

theorem exists_eigFam {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {g : ℕ} {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)}
    (he : IsTanBasis t ξ e) (σ : 𝓞 E →+* R) : ∃ U : Fin g → Fin g → R, EigFam t ξ σ e U := by
  classical
  let b := RingOfIntegers.basis E
  obtain ⟨c, hc1, hc2⟩ := exists_dual b (discr_ne_zero E)
  have hbas : ∀ w, IsTanAtG t ξ w → ∃ a, IsCombAtG t ξ e a w := fun w hw => by
    have h0 : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _
    have h1 : spMap (dualMap (RingHom.id R)) = 𝟙 _ := by
      have : dualMap (RingHom.id R) = RingHom.id _ := by ext s <;> simp [dualMap]
      rw [this]
      exact Spec.map_id _
    have := he.2 R (RingHom.id R) w (by rwa [h0, Category.id_comp])
    simp only [h0, h1, Category.id_comp] at this
    exact this.exists
  choose ρ hρ using fun (a : 𝓞 E) (k : Fin g) =>
    hbas _ (GlobalTheory.LieMet.isTan_tv (actR t.act a (GlobalTheory.LieMet.tanOf (he.1 k))))
  refine ⟨fun k j => ∑ i, σ (c i) * ρ (b i) k j, fun S _ φ => ?_⟩
  have he' := isTanBasis_bc he φ
  let T : Fin g → TanM (spMap φ ≫ ξ) t.G := fun j => GlobalTheory.LieMet.tanOf (he'.1 j)
  have hT : bcV t φ e = fun j => (tv (T j)).left := rfl
  have hA : ∀ a k, actR t.act a (T k) = ∑ j, φ (ρ a k j) • T j := fun a k => by
    refine (GlobalTheory.LieMet.isComb_iff T _ _).1 ?_
    have := GlobalTheory.GradedPieces.comb_map φ rfl (hρ a k)
    have e1 : spMap (dualMap φ) ≫ (tv (actR t.act a (GlobalTheory.LieMet.tanOf (he.1 k)))).left =
        (tv (actR t.act a (T k))).left := (Category.assoc _ _ _).symm
    rw [e1] at this
    exact this
  have hU : ∀ k, ∑ j, φ (∑ i, σ (c i) * ρ (b i) k j) • T j = ∑ i, (φ.comp σ) (c i) • actR t.act (b i) (T k) := fun k => by
    simp only [hA, map_sum, map_mul, Finset.sum_smul, Finset.smul_sum, smul_smul, RingHom.comp_apply]
    exact Finset.sum_comm
  refine ⟨fun k u hu a => ?_, fun w v hw hv => ?_⟩
  · rw [hT] at hu
    rw [eq_of_comb T hu, GlobalTheory.ShFam.Pad.Pull.eig_iff, hU]
    exact eig_proj _ _ b c hc1 a _
  · rw [hT] at hw
    have hv0 := eq_of_comb T hw
    have hv1 : ∀ a, actR t.act a (∑ i, w i • T i) = (φ.comp σ) a • ∑ i, w i • T i := fun a => by
      rw [← GlobalTheory.ShFam.Pad.Pull.eig_iff, ← hv0]
      exact hv a
    have h2 := proj_eig _ _ b c hc2 _ hv1
    have h3 : ∑ j, (∑ k, w k • fun j => φ (∑ i, σ (c i) * ρ (b i) k j)) j • T j =
        ∑ j, (((discr E : ℤ) : S) • w) j • T j := by
      have h4 : ∑ j, (((discr E : ℤ) : S) • w) j • T j = ((discr E : ℤ) : S) • ∑ j, w j • T j := by
        simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]
      rw [h4]
      refine Eq.trans ?_ h2
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_smul, mul_smul]
      rw [Finset.sum_comm]
      simp only [← Finset.smul_sum, hU]
      simp only [map_sum, map_smul, Finset.smul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => smul_comm _ _ _
    have hu := he.2 S φ _ (GlobalTheory.LieMet.isTan_tv (∑ j, (((discr E : ℤ) : S) • w) j • T j))
    have h5 := hu.unique ((GlobalTheory.LieMet.isComb_iff T _ _).2 rfl) ((GlobalTheory.LieMet.isComb_iff T _ _).2 h3.symm)
    rw [h5]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem projSt : ProjSt :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ he _ => exists_eigFam he _

end GlobalTheory.FlatModel.Proj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperFlatSectionEqZeroOfThickenings
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.SpecialConn
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.AbLaw GlobalTheory.AbLaw.Seesaw

namespace GlobalTheory.SpecialConn

theorem eq_zero_of_thickι (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (Y : Scheme.{0}) (f : Y ⟶ Spec (.of O)) [IsProper f] [Flat f]
    (s : Γ(Y, ⊤)) (hs : ∀ n, (thickι f n).appTop.hom s = 0) : s = 0 := by
  obtain ⟨P⟩ := GlobalTheory.ProperFinite.nonempty_perf_of_isProper f (Inh.trivLB_isLB Y)
  have hid : IsPullback (𝟙 Y) f f (Spec.map (CommRingCat.ofHom (RingHom.id O))) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  obtain ⟨E, hE⟩ := P.sec O (RingHom.id O) Y (𝟙 Y) f hid
  obtain ⟨w, hw⟩ := E.surjective (GlobalTheory.AlgGroup.fnSec (𝟙 Y) s)
  have key : ∀ i, rs Y (le_top : (𝟙 Y) ⁻¹ᵁ P.W i ≤ ⊤) s = loc P (𝟙 Y) f w.1 i := fun i => by
    have e := hE w i
    rw [hw] at e
    exact (rs_rs _ _ s).symm.trans e
  have key₀ : ∀ i, loc₀ P w.1 i = rs Y (le_top : P.W i ≤ ⊤) s := fun i => by
    have := (key i).trans (loc_comp P hid w.1 i)
    exact this.symm
  have hv : ∀ n k, thickQ O n (w.1 k) = 0 := by
    intro n
    have h := thickFib_isPullback f n
    obtain ⟨En, hEn⟩ := P.sec _ (thickQ O n) _ (thickι f n) (thickStr f n) h
    have hk : (P.D₀.map (thickQ O n)).mulVec (thickQ O n ∘ w.1) = 0 := funext fun j => by
      rw [← RingHom.map_mulVec]
      have := congrFun w.2 j
      rw [show P.D₀.mulVec w.1 j = 0 from this, map_zero]
      rfl
    have hz : (P.D₀.map (thickQ O n)).mulVec (0 : Fin P.a → _) = 0 := Matrix.mulVec_zero _
    have hloc : ∀ i, loc P (thickι f n) (thickStr f n) (thickQ O n ∘ w.1) i = 0 := fun i => by
      rw [loc_comp P h, key₀ i]
      have e₃ := congrArg (fun q => q.hom s) ((thickι f n).naturality (homOfLE (le_top : P.W i ≤ ⊤)).op)
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e₃
      refine e₃.trans ?_
      change rs _ _ ((thickι f n).appTop.hom s) = 0
      rw [hs n, map_zero]
    have hloc₀ : ∀ i, loc P (thickι f n) (thickStr f n) (0 : Fin P.a → _) i = 0 := fun i => by
      simp [loc]
    have heq := En.injective (a₁ := ⟨_, hk⟩) (a₂ := ⟨0, hz⟩) (sec_ext _ _
      (fun i => thickι f n ⁻¹ᵁ P.W i) (fun i _ => P.ch i) (fun i => le_pull _ _ (P.le i))
      (fun y => exists_mem P (thickι f n y)) fun i => by
        rw [hEn, hEn]
        exact (hloc i).trans (hloc₀ i).symm)
    intro k
    exact congrFun (congrArg Subtype.val heq) k
  have hw0 : ∀ k, w.1 k = 0 := fun k => by
    refine IsHausdorff.haus (I := IsLocalRing.maximalIdeal O) inferInstance (w.1 k) fun n => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    exact Ideal.pow_le_pow_right (Nat.le_succ n) (Ideal.Quotient.eq_zero_iff_mem.1 (hv n k))
  refine Y.sheaf.eq_of_locally_eq' (fun i => P.W i) ⊤ (fun i => homOfLE le_top)
    (fun y _ => TopologicalSpace.Opens.mem_iSup.2 (exists_mem P y)) s 0 fun i => ?_
  change rs Y (le_top : P.W i ≤ ⊤) s = rs Y (le_top : P.W i ≤ ⊤) 0
  rw [map_zero, ← key₀ i]
  simp [loc₀, hw0]

end GlobalTheory.SpecialConn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperSmoothGeomConnectedDescendFiniteSurjective
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

theorem surjective_to_spec_field {T : Scheme.{0}} (K : Type) [Field K] (h : T ⟶ Spec (CommRingCat.of K))
    (t : T) : Surjective h := by
  refine ⟨fun x ↦ ⟨t, ?_⟩⟩
  have : Subsingleton (PrimeSpectrum K) := inferInstance
  exact Subsingleton.elim (α := PrimeSpectrum K) _ _

theorem geometricallyConnected_of_isPullback {X X' Y Y' : Scheme.{0}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {p : X' ⟶ X}
    {q : Y' ⟶ Y} (hsq : IsPullback p f' f q) [Surjective q] [GeometricallyConnected f'] :
    GeometricallyConnected f := by
  refine ⟨fun K _ y Z fst snd hz ↦ ?_⟩
  have hb : Surjective (pullback.snd q y) :=
    MorphismProperty.of_isPullback (P := @Surjective) (IsPullback.of_hasPullback q y) inferInstance
  have k : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
  obtain ⟨z, -⟩ := (pullback.snd q y).surjective k
  let t := (pullback q y).fromSpecResidueField z
  let L := (pullback q y).residueField z
  let W := pullback f' (t ≫ pullback.fst q y)
  have hW : ConnectedSpace W :=
    GeometricallyConnected.geometrically_connectedSpace (f := f') (t ≫ pullback.fst q y)
      (pullback.fst _ _) (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
  have hbig : IsPullback (pullback.fst f' (t ≫ pullback.fst q y) ≫ p) (pullback.snd _ _) f
      ((t ≫ pullback.fst q y) ≫ q) := (IsPullback.of_hasPullback _ _).paste_horiz hsq
  have hbig' : IsPullback (pullback.fst f' (t ≫ pullback.fst q y) ≫ p) (pullback.snd _ _) f
      ((t ≫ pullback.snd q y) ≫ y) := by
    convert hbig using 1
    simp [pullback.condition]
  let w : W ⟶ Z := hz.lift (pullback.fst _ _ ≫ p) (pullback.snd _ _ ≫ t ≫ pullback.snd q y) (by
    simpa using hbig'.w)
  have hw : IsPullback w (pullback.snd f' (t ≫ pullback.fst q y)) snd (t ≫ pullback.snd q y) := by
    refine IsPullback.of_right (h₁₂ := fst) (v₁₃ := f) (h₂₂ := y) ?_ (by simp [w]) hz
    convert hbig' using 1
    simp [w]
  have hs : Surjective (t ≫ pullback.snd q y) := surjective_to_spec_field K _ (IsLocalRing.closedPoint L)
  have : Surjective w := MorphismProperty.of_isPullback (P := @Surjective) hw.flip hs
  exact w.surjective.connectedSpace w.continuous

theorem good_of_isPullback_finite_surjective : ∀ (X X' Y Y' : Scheme.{0}) (f : X ⟶ Y) (f' : X' ⟶ Y') (p : X' ⟶ X)
    (q : Y' ⟶ Y) (g : ℕ), IsPullback p f' f q → IsFinite q → Surjective q → SmoothOfRelativeDimension g f →
    GlobalTheory.DualCon.Good g f' → GlobalTheory.DualCon.Good g f := by
  intro X X' Y Y' f f' p q g hsq hq hqs hf hf'
  have := hf'.proper
  have := hf'.conn
  have : Surjective p := MorphismProperty.of_isPullback (P := @Surjective) hsq.flip hqs
  have : IsFinite p := MorphismProperty.of_isPullback (P := @IsFinite) hsq.flip hq
  have : IsProper (p ≫ f) := by rw [hsq.w]; infer_instance
  have : UniversallyClosed f := UniversallyClosed.of_comp_surjective p f
  have : IsSeparated f := GlobalTheory.NilProper.isSeparated_of_comp_surjective p f
  have : Smooth f := hf.smooth
  have : LocallyOfFiniteType f := inferInstance
  exact ⟨{}, hf, geometricallyConnected_of_isPullback hsq⟩

end GlobalTheory.DualCon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperSmoothGeomConnectedSigmaDescDisjointCover
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

theorem of_isPullback_opens_cover (Q : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget Q]
    {S X : Scheme.{0}} {I : Type} {U : I → S.Opens} (hU : iSup U = ⊤) {Z : I → Scheme.{0}} {p : X ⟶ S}
    {q : ∀ i, Z i ⟶ (U i).toScheme} {ψ : ∀ i, Z i ⟶ X} (h : ∀ i, IsPullback (ψ i) (q i) p (U i).ι)
    (hq : ∀ i, Q (q i)) : Q p := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top U hU fun i => ?_
  have e := (isPullback_morphismRestrict p (U i)).flip
  rw [← IsPullback.isoIsPullback_hom_snd _ _ e (h i), MorphismProperty.cancel_left_of_respectsIso Q]
  exact hq i

theorem isPullback_sigmaι_desc {X : Scheme.{0}} {κ : Type} (V : κ → X.Opens)
    (hd : Pairwise fun i i' => Disjoint (V i) (V i')) {B : κ → Scheme.{0}} (f : ∀ i, B i ⟶ (V i).toScheme)
    (i : κ) : IsPullback (Sigma.ι B i) (f i) (Sigma.desc fun j => f j ≫ (V j).ι) (V i).ι := by
  have : IsOpenImmersion (Sigma.ι B i) := inferInstance
  have hr : ∀ s : PullbackCone (Sigma.desc fun j => f j ≫ (V j).ι) (V i).ι,
      Set.range s.fst ⊆ Set.range (Sigma.ι B i) := by
    rintro s _ ⟨t, rfl⟩
    obtain ⟨⟨j, y⟩, hy⟩ := (sigmaMk B).surjective (s.fst t)
    rw [sigmaMk_mk] at hy
    have e1 : (Sigma.desc fun j => f j ≫ (V j).ι) (s.fst t) = (V i).ι (s.snd t) := congr($(s.condition) t)
    rw [← hy, ← Scheme.Hom.comp_apply, Sigma.ι_desc, Scheme.Hom.comp_apply] at e1
    by_cases hji : j = i
    · subst hji
      exact ⟨y, hy⟩
    · exfalso
      have h1 : (V j).ι (f j y) ∈ V j := ((V j).ι_apply _ ▸ ((f j y).2))
      have h2 : (V i).ι (s.snd t) ∈ V i := ((V i).ι_apply _ ▸ ((s.snd t).2))
      rw [e1] at h1
      have h3 := (hd hji).le_bot (show (V i).ι (s.snd t) ∈ V j ⊓ V i from ⟨h1, h2⟩)
      simp at h3
  refine ⟨⟨Sigma.ι_desc _ _⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => IsOpenImmersion.lift (Sigma.ι B i) s.fst (hr s)) ?_ ?_ ?_⟩⟩
  · intro s
    exact IsOpenImmersion.lift_fac _ _ _
  · intro s
    rw [← cancel_mono (V i).ι, Category.assoc, ← Sigma.ι_desc (fun j => f j ≫ (V j).ι) i,
      IsOpenImmersion.lift_fac_assoc, s.condition]
  · intro s m h1 _
    rw [← cancel_mono (Sigma.ι B i), IsOpenImmersion.lift_fac, h1]

theorem good_sigmaDesc_of_disjoint_cover : ∀ {X : Scheme.{0}} {κ : Type} [Finite κ] (V : κ → X.Opens), (⨆ i, V i = ⊤) → (Pairwise fun i i' => Disjoint (V i) (V i')) → ∀ {B : κ → Scheme.{0}} (f : ∀ i, B i ⟶ (V i).toScheme) (g : ℕ), (∀ i, Good g (f i)) → Good g (Sigma.desc fun i => f i ≫ (V i).ι) := by
  intro X κ _ V hU hd B f g hf
  have sq := isPullback_sigmaι_desc V hd f
  have hc : IsZariskiLocalAtTarget (@GeometricallyConnected.{0}) := by
    rw [GeometricallyConnected.eq_geometrically]; infer_instance
  have hs : IsZariskiLocalAtTarget (@SmoothOfRelativeDimension.{0} g) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _
  exact
    { proper := of_isPullback_opens_cover @IsProper hU sq fun i => (hf i).proper
      smooth := of_isPullback_opens_cover (@SmoothOfRelativeDimension.{0} g) hU sq fun i => (hf i).smooth
      conn := of_isPullback_opens_cover @GeometricallyConnected hU sq fun i => (hf i).conn }

end GlobalTheory.DualCon
end
end

