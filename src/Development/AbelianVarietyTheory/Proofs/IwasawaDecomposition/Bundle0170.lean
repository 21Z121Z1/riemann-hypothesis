import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RightTranslationActionApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0164
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0066
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0130
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0163
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0157

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteDetermining
section
noncomputable section

namespace GlobalTheory.Mem.Col2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.TopStep

section Coord

variable {K L : Type} [Field K] [Field L] (σ : K →+* L)

theorem exists_coords : ∃ (ι : Type) (e : ι → L) (c : ι → L →+ K), (∀ i k a, c i (σ k * a) = k * c i a) ∧
    ∀ a, ∃ T : Finset ι, ∀ T' : Finset ι, T ⊆ T' → ∑ i ∈ T', e i * σ (c i a) = a := by
  letI : Algebra K L := σ.toAlgebra
  let b := Module.Basis.ofVectorSpace K L
  refine ⟨_, b, fun i => (b.coord i).toAddMonoidHom, fun i k a => ?_, fun a => ⟨(b.repr a).support, fun T' hT => ?_⟩⟩
  · exact (b.coord i).map_smul k a
  · conv_rhs => rw [← b.linearCombination_repr a, Finsupp.linearCombination_apply,
      Finsupp.sum_of_support_subset _ hT _ (by simp)]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _

variable {I : Type}

def coefMap (c : L →+ K) (p : MvPolynomial I L) : MvPolynomial I K :=
  ∑ m ∈ p.support, MvPolynomial.monomial m (c (p.coeff m))

theorem coeff_coefMap (c : L →+ K) (p : MvPolynomial I L) (m : I →₀ ℕ) : (coefMap c p).coeff m = c (p.coeff m) := by
  classical
  simp only [coefMap, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.1 h, map_zero]

theorem coefMap_add (c : L →+ K) (p q : MvPolynomial I L) : coefMap c (p + q) = coefMap c p + coefMap c q := by
  ext m
  simp only [coeff_coefMap, MvPolynomial.coeff_add, map_add]

theorem coefMap_zero (c : L →+ K) : coefMap c (0 : MvPolynomial I L) = 0 := by
  ext m
  simp only [coeff_coefMap, MvPolynomial.coeff_zero, map_zero]

theorem coefMap_sum {J : Type*} (c : L →+ K) (s : Finset J) (p : J → MvPolynomial I L) :
    coefMap c (∑ j ∈ s, p j) = ∑ j ∈ s, coefMap c (p j) := by
  ext m
  simp only [coeff_coefMap, MvPolynomial.coeff_sum, map_sum]

variable {σ}

theorem coefMap_smul_map {c : L →+ K} (hc : ∀ k a, c (σ k * a) = k * c a) (a : L) (p : MvPolynomial I K) :
    coefMap c (a • MvPolynomial.map σ p) = c a • p := by
  ext m
  rw [coeff_coefMap, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul, MvPolynomial.coeff_map, smul_eq_mul, smul_eq_mul,
    mul_comm, hc, mul_comm]

theorem coefMap_smul {c : L →+ K} (hc : ∀ k a, c (σ k * a) = k * c a) (k : K) (p : MvPolynomial I L) :
    coefMap c (σ k • p) = k • coefMap c p := by
  ext m
  rw [coeff_coefMap, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul, coeff_coefMap, smul_eq_mul, smul_eq_mul, hc]

theorem exists_sum_coefMap {ι : Type} {e : ι → L} {c : ι → L →+ K}
    (h : ∀ a, ∃ T : Finset ι, ∀ T' : Finset ι, T ⊆ T' → ∑ i ∈ T', e i * σ (c i a) = a) (p : MvPolynomial I L) :
    ∃ T : Finset ι, ∀ T' : Finset ι, T ⊆ T' → ∑ i ∈ T', e i • MvPolynomial.map σ (coefMap (c i) p) = p := by
  classical
  choose T hT using h
  refine ⟨p.support.biUnion fun m => T (p.coeff m), fun T' hT' => ?_⟩
  ext m
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, MvPolynomial.coeff_map, coeff_coefMap, smul_eq_mul]
  by_cases hm : m ∈ p.support
  · exact hT _ _ ((Finset.subset_biUnion_of_mem (fun m => T (p.coeff m)) hm).trans hT')
  · simp [MvPolynomial.notMem_support_iff.1 hm]

variable (σ)

theorem linearIndependent_map_pi {D J : Type*} {f : J → D → MvPolynomial I K} (hf : LinearIndependent K f) :
    LinearIndependent L fun j d => MvPolynomial.map σ (f j d) := by
  obtain ⟨ι, e, c, hc, h⟩ := exists_coords σ
  rw [linearIndependent_iff'] at hf ⊢
  intro s g hg j hj
  have h0 : ∀ i, c i (g j) = 0 := fun i => by
    refine hf s (fun j => c i (g j)) (funext fun d => ?_) j hj
    have h1 := congrArg (coefMap (c i)) (congrFun hg d)
    rw [Finset.sum_apply, coefMap_sum, Pi.zero_apply, coefMap_zero] at h1
    rw [Finset.sum_apply, Pi.zero_apply, ← h1]
    exact Finset.sum_congr rfl fun k _ => (coefMap_smul_map (hc i) _ _).symm
  obtain ⟨T, hT⟩ := h (g j)
  rw [← hT T le_rfl]
  simp [h0]

theorem VV_induction {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) {P : Pol L ι n → Prop} (h0 : P 0)
    (hadd : ∀ x y, P x → P y → P (x + y)) (hs : ∀ (a : L) (v : VV K lam), P (a • MvPolynomial.map σ v.1))
    (x : Pol L ι n) (hx : x ∈ VV L lam) : P x := by
  have e : x = ∑ i, (bVV L lam).repr ⟨x, hx⟩ i • bVVfun L lam i := by
    conv_lhs => rw [show x = ((⟨x, hx⟩ : VV L lam) : Pol L ι n) from rfl, ← (bVV L lam).sum_repr ⟨x, hx⟩]
    simp only [Submodule.coe_sum, Submodule.coe_smul, bVV_coe]
  rw [e]
  refine Finset.sum_induction _ P hadd h0 fun i _ => ?_
  obtain ⟨F, hF, hF'⟩ := GlobalTheory.Proof.TensorMapDescent.bVVfun_desc σ lam i
  rw [hF']
  exact hs _ ⟨F, hF⟩

variable {σ}

theorem coefMap_mem_VV {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) {c : L →+ K}
    (hc : ∀ k a, c (σ k * a) = k * c a) (x : Pol L ι n) (hx : x ∈ VV L lam) : coefMap c x ∈ VV K lam := by
  refine VV_induction σ lam (P := fun x => coefMap c x ∈ VV K lam) ?_ (fun x y hx hy => ?_) (fun a v => ?_) x hx
  · rw [coefMap_zero]; exact zero_mem _
  · rw [coefMap_add]; exact add_mem hx hy
  · rw [coefMap_smul_map hc]; exact Submodule.smul_mem _ _ v.2

end Coord

section CForms

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (σ : X.K →+* ℂ) (lam : X.Tau → DomWeight n)

theorem coefMap_rhoC {c : ℂ →+ X.K} (hc : ∀ k a, c (σ k * a) = k * c a) (γ : UF X.E n) (x : Pol ℂ X.Tau n)
    (hx : x ∈ VV ℂ lam) :
    coefMap c (rhoC σ lam γ x) = (rhoV X.emb lam (ufGL X.E n γ) ⟨coefMap c x, coefMap_mem_VV lam hc x hx⟩).1 := by
  have h : ∃ y : VV X.K lam, y.1 = coefMap c x ∧ coefMap c (rhoC σ lam γ x) = (rhoV X.emb lam (ufGL X.E n γ) y).1 := by
    refine VV_induction σ lam (P := fun x => ∃ y : VV X.K lam, y.1 = coefMap c x ∧
      coefMap c (rhoC σ lam γ x) = (rhoV X.emb lam (ufGL X.E n γ) y).1) ⟨0, (coefMap_zero c).symm, ?_⟩ ?_ ?_ x hx
    · rw [map_zero, coefMap_zero, map_zero]
      rfl
    · rintro x y ⟨u, hu, hu'⟩ ⟨v, hv, hv'⟩
      refine ⟨u + v, by rw [coefMap_add, ← hu, ← hv]; rfl, ?_⟩
      rw [map_add, coefMap_add, hu', hv', map_add]
      rfl
    · intro a v
      refine ⟨c a • v, (coefMap_smul_map hc a v.1).symm, ?_⟩
      rw [map_smul, rhoC_map, coefMap_smul_map hc, map_smul]
      rfl
  obtain ⟨y, hy, h⟩ := h
  rw [h]
  exact congrArg (fun z => (rhoV X.emb lam (ufGL X.E n γ) z).1) (Subtype.ext hy)

variable (L : DecoSet X.E n ST SG → Submodule (𝓞 X.E) (Sp X.E n)) (Λ : LevFam X.E X.K n SG)

def coordForm {c : ℂ →+ X.K} (hc : ∀ k a, c (σ k * a) = k * c a) (F : cForms ST σ lam Λ) :
    (formGSD (squarePk X lam L) Λ).EqFun :=
  ⟨fun d => ⟨coefMap c (F.1 d), coefMap_mem_VV lam hc _ (F.2 d).1⟩, fun g d => Subtype.ext <| by
    refine (congrArg (coefMap c) ((F.2 d).2 g)).trans ?_
    rw [coefMap_smul hc, coefMap_rhoC σ lam hc _ _ (F.2 d).1]
    rfl⟩

theorem toCForm_linearIndependent {J : Type*} {φ : J → (formGSD (squarePk X lam L) Λ).EqFun} (h : LinearIndependent X.K φ) :
    LinearIndependent ℂ fun j => toCForm σ lam L Λ (φ j) := by
  refine LinearIndependent.of_comp (cForms ST σ lam Λ).subtype ?_
  let i : (formGSD (squarePk X lam L) Λ).EqFun →ₗ[X.K] (DecoSet X.E n ST SG → Pol X.K X.Tau n) :=
    { toFun := fun φ d => (φ.1 d).1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hi : Function.Injective i := fun _ _ e => Subtype.ext (funext fun d => Subtype.ext (congrFun e d))
  exact linearIndependent_map_pi σ (h.map' i (LinearMap.ker_eq_bot.2 hi))

theorem exists_finite_determining (hX : X.Ok) : ∃ s : Set (DecoSet X.E n ST SG), s.Finite ∧
    ∀ F : cForms ST σ lam Λ, (∀ d ∈ s, F.1 d = 0) → F = 0 := by
  obtain ⟨s, hs, hrep⟩ := DecoSet.finite_reps (ST := ST) (SG := SG) (n := n) (posStar_of_conj hX.conjE)
  refine ⟨s, hs, fun F hF => Subtype.ext (funext fun d => ?_)⟩
  obtain ⟨d0, hd0, g, rfl⟩ := hrep d
  have h := ((mem_cForms σ lam Λ F.1).1 F.2 d0).2 g 1
  rw [hF d0 hd0, map_zero, smul_zero] at h
  exact h

theorem toCForm_span (hX : X.Ok) : Submodule.span ℂ (Set.range (toCForm σ lam L Λ)) = ⊤ := by
  classical
  obtain ⟨ι, e, c, hc, h⟩ := exists_coords σ
  obtain ⟨s, hs, hdet⟩ := exists_finite_determining (ST := ST) σ lam Λ hX
  refine eq_top_iff.2 fun F _ => ?_
  choose T hT using fun d => exists_sum_coefMap h (F.1 d)
  have e1 : F = ∑ i ∈ hs.toFinset.biUnion T, e i • toCForm σ lam L Λ (coordForm σ lam L Λ (hc i) F) := by
    refine sub_eq_zero.1 (hdet _ fun d hd => ?_)
    rw [Submodule.coe_sub, Pi.sub_apply, Submodule.coe_sum, Finset.sum_apply, sub_eq_zero]
    exact (hT d _ (Finset.subset_biUnion_of_mem T (hs.mem_toFinset.2 hd))).symm
  rw [e1]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem toCForm_span_of_span (hX : X.Ok) {J : Type*} {φ : J → (formGSD (squarePk X lam L) Λ).EqFun}
    (h : Submodule.span X.K (Set.range φ) = ⊤) : Submodule.span ℂ (Set.range fun j => toCForm σ lam L Λ (φ j)) = ⊤ := by
  refine eq_top_iff.2 ((toCForm_span σ lam L Λ hX).ge.trans (Submodule.span_le.2 ?_))
  rintro _ ⟨ψ, rfl⟩
  have hψ : ψ ∈ Submodule.span X.K (Set.range φ) := h ▸ trivial
  induction hψ using Submodule.span_induction with
  | mem x hx => obtain ⟨j, rfl⟩ := hx; exact Submodule.subset_span ⟨j, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

def basisCForm (hX : X.Ok) {J : Type*} (b : Module.Basis J X.K (formGSD (squarePk X lam L) Λ).EqFun) :
    Module.Basis J ℂ (cForms ST σ lam Λ) :=
  Module.Basis.mk (toCForm_linearIndependent σ lam L Λ b.linearIndependent) (toCForm_span_of_span σ lam L Λ hX b.span_eq).ge

theorem basisCForm_apply (hX : X.Ok) {J : Type*} (b : Module.Basis J X.K (formGSD (squarePk X lam L) Λ).EqFun) (j : J) :
    basisCForm σ lam L Λ hX b j = toCForm σ lam L Λ (b j) := Module.Basis.mk_apply _ _ _

theorem rank_cForms (hX : X.Ok) :
    Module.rank ℂ (cForms ST σ lam Λ) = Module.rank X.K (formGSD (squarePk X lam L) Λ).EqFun := by
  let b := Module.Basis.ofVectorSpace X.K (formGSD (squarePk X lam L) Λ).EqFun
  rw [← b.mk_eq_rank'', ← (basisCForm σ lam L Λ hX b).mk_eq_rank'']

theorem finrank_cForms (hX : X.Ok) :
    Module.finrank ℂ (cForms ST σ lam Λ) = Module.finrank X.K (formGSD (squarePk X lam L) Λ).EqFun :=
  congrArg Cardinal.toNat (rank_cForms σ lam L Λ hX)

end CForms

section Rows

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) (σ : X.K →+* ℂ)

theorem toMtilde_linearIndependent {J : Type*} {φ : J → MtildeV W Ch sel mu P} (h : LinearIndependent X.K φ) :
    LinearIndependent ℂ fun j => toMtP W Ch sel mu P σ (φ j) := toCForm_linearIndependent σ W.sgTrue _ _ h

theorem toMtilde_span (hX : X.Ok) : Submodule.span ℂ (Set.range (toMtP W Ch sel mu P σ)) = ⊤ := toCForm_span σ W.sgTrue _ _ hX

theorem finrank_MtP (hX : X.Ok) : Module.finrank ℂ (MtP W Ch sel mu P σ) = Module.finrank X.K (MtildeV W Ch sel mu P) :=
  finrank_cForms σ W.sgTrue _ _ hX

end Rows

end GlobalTheory.Mem.Col2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelGroupModTypePrime
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

noncomputable section

namespace GlobalTheory.Mem.Col2.LevMod

open GlobalTheory.CongLevel

section Red

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E))

def RedTo (g : Sp E n ≃ₗ[E] Sp E n) (hbar : GL (Fin n) (𝓞 E ⧸ P.asIdeal)) : Prop :=
  ∀ x ∈ stdAt E n P, redV P (g x) = hbar.1.mulVec (redV P x)

variable {P}

theorem RedTo.one : RedTo P (1 : Sp E n ≃ₗ[E] Sp E n) 1 := fun x _ => by
  rw [Units.val_one, Matrix.one_mulVec]; rfl

theorem RedTo.mul {g g' : Sp E n ≃ₗ[E] Sp E n} {a b : GL (Fin n) (𝓞 E ⧸ P.asIdeal)} (hg' : g' ∈ GLint E n P)
    (h : RedTo P g a) (h' : RedTo P g' b) : RedTo P (g * g') (a * b) := fun x hx => by
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← h' x hx]
  exact h _ ((hg' x).2 hx)

theorem RedTo.inv {g : Sp E n ≃ₗ[E] Sp E n} {a : GL (Fin n) (𝓞 E ⧸ P.asIdeal)} (hg : g ∈ GLint E n P)
    (h : RedTo P g a) : RedTo P g⁻¹ a⁻¹ := fun x hx => by
  have h1 := h _ (((inv_mem hg : g⁻¹ ∈ GLint E n P) x).2 hx)
  rw [show g (g⁻¹ x) = x from g.apply_symm_apply x] at h1
  rw [h1, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

variable (P) in

def redSub (G : Subgroup (Sp E n ≃ₗ[E] Sp E n)) (hG : G ≤ GLint E n P) : Subgroup (GL (Fin n) (𝓞 E ⧸ P.asIdeal)) where
  carrier := {a | ∃ g ∈ G, RedTo P g a}
  one_mem' := ⟨1, one_mem _, RedTo.one⟩
  mul_mem' := fun ⟨g, hg, h⟩ ⟨g', hg', h'⟩ => ⟨g * g', mul_mem hg hg', RedTo.mul (hG hg') h h'⟩
  inv_mem' := fun ⟨g, hg, h⟩ => ⟨g⁻¹, inv_mem hg, h.inv (hG hg)⟩

end Red

theorem unipotentArg_extendByIdOnLastCoords {E : Type} [Field E] {n : ℕ} (c : ℕ) (κ : (Fin n → E) ≃ₗ[E] (Fin n → E)) :
    Loc.n1Arg (extE c κ) = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [add_assoc, extE_apply, resX_eN]
  simp only [map_zero, sub_self, add_zero]
  unfold Loc.atN Loc.eN
  split_ifs with h1 h2
  · exact absurd h2 (by simp)
  · rfl
  · rfl

variable {X : Fields} {Pr : Primes X} {R : Ranks}

theorem extE_mem_Cbe (sharp : Bool) (j : ℕ) (w : HeightOneSpectrum (𝓞 X.E)) (hw : w ∈ Pr.vGs)
    (hd : ∀ a : X.E, IntAt w a → redP w a = 0 → IntAt w (a / (qOf w : X.E))) (h : AutY X R j)
    (hh : h ∈ stabL X.E _ (lamYat (Pr := Pr) j w)) (κ : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j))
    (hκ : κ ∈ GLint X.E (R.N j) w) (hr : ∀ x ∈ stdAt X.E (R.N j) w, redV w (κ x) = redV w x) :
    extE (cOf R j) κ ∈ Loc.Cbe (Jat (Pr := Pr) sharp j w) h := by
  have hq : ((qOf w : ℕ) : X.E) ≠ 0 := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero w
  unfold lamYat at hh
  rw [if_pos hw] at hh
  refine ⟨extendByIdOnLastCoordsLinearEquiv_mem_firstRowGroup _ κ, ?_⟩
  have e : (MulAut.conj h⁻¹).toMonoidHom (extE (cOf R j) κ) = h⁻¹ * extE (cOf R j) κ * h := by simp
  show (MulAut.conj h⁻¹).toMonoidHom (extE (cOf R j) κ) ∈ Jat (Pr := Pr) sharp j w
  rw [e]
  have hs := mul_mem (mul_mem (inv_mem hh) (extE_stab w (qOf w) (cOf R j) (fun i => i + 1) κ hκ)) hh
  have hc := conj_cong (qOf w) _ _ h hh (extE_cong w (qOf w) (cOf R j) (fun i => i + 1) hd κ hκ hr)
  unfold Jat
  rw [if_pos hw]
  split_ifs
  · refine ⟨hs, mem_flagU (qOf w) _ _ _ _ _ (fun s => ?_) (fun s x hx => ?_) (fun s => ?_) _ hs hc⟩
    · exact CongLevel.sclLat_le w _ hq _ _ _
    · exact smul_mem_sclLat w _ hq _ _ _ x hx
    · exact bvec_mem w _ hq _ _ _
  · refine ⟨hs, mem_flagU (qOf w) _ _ _ _ _ (fun s => ?_) (fun s x hx => ?_) (fun s => ?_) _ hs hc⟩
    · exact CongLevel.sclLat_le w _ hq _ _ _
    · exact smul_mem_sclLat w _ hq _ _ _ x hx
    · exact bvec_mem w _ hq _ _ _

theorem exists_levG : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (j : ℕ) (P : rowSG Pr sel mu) (h : AutY X R j), cst.Ok → P.1 ∈ Pr.vGs → GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P.1 → h ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P.1) → prCat (Pr := Pr) cst.sharp j P.1 h ≤ GLint X.E (R.N j) P.1 → (∀ y : HomE X.E (R.N j + cOf R j) (R.N j + cOf R j), (∀ x ∈ lamYat (Pr := Pr) (R := R) j P.1, y x ∈ lamYat (Pr := Pr) (R := R) j P.1) → lamRow Ch mu cst.sharp j P.1 (LinearMap.id + (qOf P.1 : X.E) • y) = 1) → ChiMul Ch sel mu cst j P h → ChiTriv Ch sel mu cst j P h → ∃ lev : Lev (𝓞 X.E ⧸ P.1.asIdeal) X.K (R.N j), GrpG sel mu cst j P h lev ∧ ChrG Ch sel mu cst j P h lev := by
  intro X Pr R Ch sel S mu cst j P h hc hP hdu hh hle hlam hmul htriv
  have hq : ((qOf P.1 : ℕ) : X.E) ≠ 0 := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P.1
  have hd : ∀ a : X.E, IntAt P.1 a → redP P.1 a = 0 → IntAt P.1 (a / (qOf P.1 : X.E)) := fun a ha h0 => by
    have := GlobalTheory.TypePrimeUnif.intAt_div_of_notMem_sq P.1 _ (Ideal.absNorm_mem _) hdu.2 a ha h0
    rwa [map_natCast] at this
  have hone : ∀ κ ∈ GLint X.E (R.N j) P.1, (∀ x ∈ stdAt X.E (R.N j) P.1, redV P.1 (κ x) = redV P.1 x) →
      chiInv Ch sel mu cst j P h (extE (cOf R j) κ) = 1 := by
    intro κ hκ hr
    unfold lamYat at hh hlam
    rw [if_pos hP] at hh hlam
    have hcong := conj_cong (qOf P.1) _ _ h hh
      (extE_cong P.1 (qOf P.1) (cOf R j) (fun i => i + 1) hd κ hκ hr)
    have h1 := hlam ((qOf P.1 : X.E)⁻¹ • ((h⁻¹ * extE (cOf R j) κ * h : AutY X R j).toLinearMap - LinearMap.id))
      fun x hx => by
        have h2 := hcong x hx
        rw [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe]
        exact h2
    rw [smul_inv_smul₀ hq, add_sub_cancel] at h1
    unfold chiInv
    rw [h1, unipotentArg_extendByIdOnLastCoords, hc.psi_int P 0 (by simpa using CongLevel.intAt_nat P.1 0), inv_one, one_mul]
  obtain ⟨lam, hl⟩ := exists_char (H := ↥(redSub P.1 _ hle)) (CAt sel mu cst j P h) (chiInv Ch sel mu cst j P h)
    (fun r a => ∃ g ∈ GLint X.E (R.N j) P.1,
      (∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (g x)) ∧ RedTo P.1 g a.1)
    hmul.1 hmul.2
    (fun ⟨a, g, hg, hga⟩ => by
      obtain ⟨r, hr, hrg⟩ := id hg
      exact ⟨r, hr, g, hle hg, hrg, hga⟩)
    (by
      rintro r a r' a' ⟨g, hg, h1, h2⟩ ⟨g', hg', h1', h2'⟩
      refine ⟨g * g', mul_mem hg hg', fun x => ?_, RedTo.mul hg' h2 h2'⟩
      show r (r' _) = _
      rw [h1', h1]
      rfl)
    (by
      rintro a r hr r' hr' ⟨g, hg, h1, h2⟩ ⟨g', hg', h1', h2'⟩
      have hκ : g⁻¹ * g' ∈ GLint X.E (R.N j) P.1 := mul_mem (inv_mem hg) hg'
      have hred : ∀ x ∈ stdAt X.E (R.N j) P.1, redV P.1 ((g⁻¹ * g') x) = redV P.1 x := fun x hx => by
        rw [RedTo.mul hg' (h2.inv hg) h2' x hx, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      have hs : extE (cOf R j) (g⁻¹ * g') ∈ CAt sel mu cst j P h := extE_mem_Cbe _ j P.1 hP hd h hh _ hκ hred
      have ht : (extE (cOf R j) (g⁻¹ * g'))⁻¹ * (r⁻¹ * r') ∈ CAt sel mu cst j P h :=
        mul_mem (inv_mem hs) (mul_mem (inv_mem hr) hr')
      have ht1 := htriv _ ht fun x => by
        show (extE (cOf R j) (g⁻¹ * g')).symm (r.symm (r' _)) = _
        rw [LinearEquiv.symm_apply_eq, LinearEquiv.symm_apply_eq, extE_inX, h1, h1']
        exact congrArg _ (g.apply_symm_apply _).symm
      have e : r' = r * (extE (cOf R j) (g⁻¹ * g') * ((extE (cOf R j) (g⁻¹ * g'))⁻¹ * (r⁻¹ * r'))) := by
        rw [mul_inv_cancel_left, mul_inv_cancel_left]
      have h3 := hmul.2 r hr _ (mul_mem hs ht)
      rw [← e, hmul.2 _ hs _ ht, ht1, hone _ hκ hred, mul_one, mul_one] at h3
      exact h3.symm)
  exact ⟨⟨redSub P.1 _ hle, lam⟩, fun _ => Iff.rfl,
    fun a g r hr h1 h2 => hl a r hr ⟨g, hle ⟨r, hr, h1⟩, h1, h2⟩⟩

end GlobalTheory.Mem.Col2.LevMod

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMorphismOfStalkMaps
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GlueStalk

theorem isDominant_fromSpecStalk_of_isIntegral (X : Scheme.{0}) [IsIntegral X] (x : X) :
    IsDominant (X.fromSpecStalk x) := by
  refine ⟨?_⟩
  have h : genericPoint X ∈ Set.range (X.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact (genericPoint_spec X).specializes trivial
  have h2 : Dense ({genericPoint X} : Set X) := by
    rw [dense_iff_closure_eq]; exact genericPoint_spec X
  exact h2.mono (Set.singleton_subset_iff.2 h)

theorem fromSpecStalk_generic {T S P : Scheme.{0}} (h : ∀ x : T, Spec (T.presheaf.stalk x) ⟶ S)
    (H : ∀ (x ξ : T) (e : ξ ⤳ x), (∀ y, y ⤳ ξ → y = ξ) → Spec.map (T.presheaf.stalkSpecializes e) ≫ h x = h ξ)
    (V : T.Opens) [IsIntegral V] {x : T} (hx : x ∈ V) (f : V.toScheme ⟶ S)
    (hf : V.fromSpecStalkOfMem x hx ≫ f = h x) [IsIntegral P] (j : P ⟶ V) (k : P ⟶ T) [IsOpenImmersion k]
    (hk : j ≫ V.ι = k) :
    P.fromSpecStalk (genericPoint P) ≫ j ≫ f =
      Spec.map (k.stalkMap (genericPoint P)) ≫ h (k (genericPoint P)) := by
  have hmax : ∀ y, y ⤳ k (genericPoint P) → y = k (genericPoint P) := fun y hy => by
    obtain ⟨p, rfl⟩ : y ∈ Set.range k := hy.mem_open k.isOpenEmbedding.isOpen_range ⟨_, rfl⟩
    exact (hy.antisymm (((genericPoint_spec P).specializes trivial).map k.continuous)).eq
  have e₀ : V.ι (genericPoint V) = k (genericPoint P) := hmax _ (by
    rw [← hk, Scheme.Hom.comp_apply]
    exact ((genericPoint_spec V).specializes trivial).map V.ι.continuous)
  have e : k (genericPoint P) ⤳ x := by
    rw [← e₀]
    exact ((genericPoint_spec V).specializes (y := (⟨x, hx⟩ : V)) trivial).map V.ι.continuous
  rw [← H x _ e hmax, ← hf, ← Category.assoc, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [← cancel_mono V.ι, Category.assoc, hk, Category.assoc, Category.assoc,
    Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

theorem exists_glue_of_stalks : ∀ (B T S : Scheme.{0}) (t : T ⟶ B) (s : S ⟶ B) (h : ∀ x : T, Spec (T.presheaf.stalk x) ⟶ S), LocallyOfFiniteType s → IsSeparated s → IsLocallyNoetherian T → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme T → (∀ x, h x ≫ s = T.fromSpecStalk x ≫ t) → (∀ (x ξ : T) (e : ξ ⤳ x), (∀ y, y ⤳ ξ → y = ξ) → Spec.map (T.presheaf.stalkSpecializes e) ≫ h x = h ξ) → ∃ g : T ⟶ S, ∀ x, T.fromSpecStalk x ≫ g = h x := by
  intro B T S t s h _ _ _ hn hs H
  have : GlobalTheory.IsNormalScheme T := GlobalTheory.IsNormalScheme.of_pred hn
  have loc : ∀ x : T, ∃ (V : T.Opens) (hx : x ∈ V) (f : V.toScheme ⟶ S), IsIntegral V ∧
      V.fromSpecStalkOfMem x hx ≫ f = h x ∧ f ≫ s = V.ι ≫ t := fun x => by
    obtain ⟨U, hU, f, h₁, h₂⟩ := spread_out_of_isGermInjective' t s (h x) (hs x)
    let Z : irreducibleComponents T := ⟨_, irreducibleComponent_mem_irreducibleComponents x⟩
    have hx : x ∈ U ⊓ GlobalTheory.IsNormalScheme.component Z := ⟨hU, mem_irreducibleComponent⟩
    have : Nonempty (U ⊓ GlobalTheory.IsNormalScheme.component Z).toScheme := ⟨⟨x, hx⟩⟩
    refine ⟨_, hx, T.homOfLE inf_le_left ≫ f, isIntegral_of_isOpenImmersion (T.homOfLE inf_le_right), ?_, ?_⟩
    · rw [h₁, ← Category.assoc]
      congr 1
      rw [← cancel_mono U.ι, Category.assoc, Scheme.homOfLE_ι, Scheme.Opens.fromSpecStalkOfMem_ι,
        Scheme.Opens.fromSpecStalkOfMem_ι]
    · rw [Category.assoc, h₂, Scheme.homOfLE_ι_assoc]
  choose V hx f hi h₁ h₂ using loc
  have hc : ⨆ x, V x = ⊤ := top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hx x⟩
  have key : ∀ x y, pullback.fst (V x).ι (V y).ι ≫ f x = pullback.snd (V x).ι (V y).ι ≫ f y := fun x y => by
    have := hi x
    have := hi y
    cases isEmpty_or_nonempty ↥(pullback (V x).ι (V y).ι) with
    | inl _ => exact (isInitialOfIsEmpty (X := pullback (V x).ι (V y).ι)).hom_ext _ _
    | inr _ =>
      have : IsIntegral (pullback (V x).ι (V y).ι) := isIntegral_of_isOpenImmersion (pullback.fst (V x).ι (V y).ι)
      have := isDominant_fromSpecStalk_of_isIntegral _ (genericPoint ↥(pullback (V x).ι (V y).ι))
      refine ext_of_isDominant_of_isSeparated s ?_
        ((pullback (V x).ι (V y).ι).fromSpecStalk (genericPoint _)) ?_
      · rw [Category.assoc, Category.assoc, h₂, h₂, pullback.condition_assoc]
      · exact (fromSpecStalk_generic h H (V x) (hx x) (f x) (h₁ x) _ _ rfl).trans
          (fromSpecStalk_generic h H (V y) (hx y) (f y) (h₁ y) _ _ pullback.condition.symm).symm
  refine ⟨(T.openCoverOfIsOpenCover V hc).glueMorphisms f key, fun x => ?_⟩
  rw [← Scheme.Opens.fromSpecStalkOfMem_ι (V x) x (hx x), Category.assoc, ← h₁ x]
  exact congrArg (_ ≫ ·) (Scheme.Cover.ι_glueMorphisms (T.openCoverOfIsOpenCover V hc) f key x)

end GlobalTheory.GlueStalk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPlaceIsTeichmullerLiftFbar
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting

noncomputable section
namespace GlobalTheory.TeichPlace

theorem exists_place_isTeich : ∀ (g : ℕ) [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* ℂ), (∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) → ∃ (A : ValuationSubring ℂ) (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g), IsTeich A κ t := by
  intro g _ t ht
  obtain ⟨ι⟩ := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex g
  obtain ⟨κ₀⟩ := GlobalTheory.HeightCounting.nonempty_residueField_unitBall_equiv ι
  obtain ⟨t₀, ht₀, hinj₀⟩ := GlobalTheory.T.exists_teichmuller_reindex_complexPlace g (GlobalTheory.HeightCounting.unitBall ι) κ₀ t ht
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.fbar_exists_complexAut_comp_eq g t t₀ ht hinj₀
  let A : ValuationSubring ℂ := (GlobalTheory.HeightCounting.unitBall ι).comap (σ.symm : ℂ →+* ℂ)
  have hmem : ∀ z : ℂ, z ∈ A ↔ σ.symm z ∈ GlobalTheory.HeightCounting.unitBall ι := fun z => ValuationSubring.mem_comap
  let e : A ≃+* GlobalTheory.HeightCounting.unitBall ι :=
    { toFun := fun a => ⟨σ.symm a, (hmem a).1 a.2⟩
      invFun := fun b => ⟨σ b, (hmem _).2 (by simpa using b.2)⟩
      left_inv := fun a => Subtype.ext (by simp)
      right_inv := fun b => Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  refine ⟨A, (IsLocalRing.ResidueField.mapEquiv e).trans κ₀, fun x => ?_⟩
  have hx : σ.symm (t x) = t₀ x := by rw [← hσ x, RingEquiv.symm_apply_apply]
  obtain ⟨h₀, e₀⟩ := ht₀ x
  refine ⟨(hmem _).2 (hx ▸ h₀), ?_⟩
  refine Eq.trans ?_ e₀
  change κ₀ (IsLocalRing.ResidueField.map (e : A →+* GlobalTheory.HeightCounting.unitBall ι) (IsLocalRing.residue A _)) = _
  rw [IsLocalRing.ResidueField.map_residue]
  congr 2
  exact Subtype.ext hx

end GlobalTheory.TeichPlace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimeOverSplitNotMemConjStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_over_split_not_mem_conj : ∀ (R : Ranks) (H : Host R) (p : ℕ), p.Prime → Th.SplitK H p → ∃ (𝔭 : HeightOneSpectrum (𝓞 H.K)) (α β : 𝓞 H.K), (p : 𝓞 H.K) ∈ 𝔭.asIdeal ∧ α ∈ 𝔭.asIdeal ∧ β ∉ 𝔭.asIdeal ∧ (β : H.K) = HostK.conjK H α := by
  first | exact @GlobalTheory.Mem.Col2.SplitPrime.exists_prime_not_conj | exact GlobalTheory.Mem.Col2.SplitPrime.exists_prime_not_conj | (intros; apply GlobalTheory.Mem.Col2.SplitPrime.exists_prime_not_conj <;> assumption)
end

