import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1144
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1097
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1122
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1145
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0182
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearActionDualWeylTensor
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulVecEqPow
section
set_option autoImplicit false

noncomputable section

open PowerSeries Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange

namespace GlobalTheory.WachPlace

section Columns

variable {F : Type} [Field F] {a b c : ℕ}

def vecL (y : Fin a → F⟦X⟧) : Fin a → LaurentSeries F := fun j => algebraMap F⟦X⟧ (LaurentSeries F) (y j)

def linL (A : Mx F⟦X⟧ a b) : (Fin b → LaurentSeries F) →ₗ[LaurentSeries F] (Fin a → LaurentSeries F) :=
  (A.map (algebraMap F⟦X⟧ (LaurentSeries F))).mulVecLin

def colL (A : Mx F⟦X⟧ a b) : Submodule (LaurentSeries F) (Fin a → LaurentSeries F) := LinearMap.range (linL A)

theorem finrank_colL (A : Mx F⟦X⟧ a b) : Module.finrank (LaurentSeries F) (colL A) = lrank A := rfl

theorem linL_vecL (A : Mx F⟦X⟧ a b) (y : Fin b → F⟦X⟧) : linL A (vecL y) = vecL (A.mulVec y) := by
  funext j
  exact (RingHom.map_mulVec (algebraMap F⟦X⟧ (LaurentSeries F)) A y j).symm

theorem linL_mul (A : Mx F⟦X⟧ a b) (B : Mx F⟦X⟧ b c) : linL (A * B) = (linL A).comp (linL B) := by
  rw [linL, Matrix.map_mul, Matrix.mulVecLin_mul]
  rfl

theorem vecL_smul (s : F⟦X⟧) (y : Fin a → F⟦X⟧) : vecL (s • y) = algebraMap F⟦X⟧ (LaurentSeries F) s • vecL y := by
  funext j
  simp only [vecL, Pi.smul_apply, smul_eq_mul, map_mul]

theorem vecL_sub (y z : Fin a → F⟦X⟧) : vecL (y - z) = vecL y - vecL z := by
  funext j
  simp only [vecL, Pi.sub_apply, map_sub]

theorem vecL_injective : Function.Injective (vecL : (Fin a → F⟦X⟧) → _) := fun _ _ h =>
  funext fun j => IsFractionRing.injective F⟦X⟧ (LaurentSeries F) (congrFun h j)

theorem colL_mul_le (A : Mx F⟦X⟧ a b) (B : Mx F⟦X⟧ b c) : colL (A * B) ≤ colL A := by
  rw [colL, linL_mul]
  exact LinearMap.range_comp_le_range _ _

theorem colL_eq_top {A : Mx F⟦X⟧ a b} (h : lrank A = a) : colL A = ⊤ :=
  Submodule.eq_top_of_finrank_eq (by rw [finrank_colL, h, Module.finrank_fin_fun])

theorem colL_mul_eq (A : Mx F⟦X⟧ a b) {B : Mx F⟦X⟧ b c} (h : lrank B = b) : colL (A * B) = colL A := by
  rw [colL, linL_mul]
  exact LinearMap.range_comp_of_range_eq_top _ (colL_eq_top h)

theorem exists_clear (z : Fin a → LaurentSeries F) :
    ∃ (m : ℕ) (w : Fin a → F⟦X⟧), vecL w = algebraMap F⟦X⟧ (LaurentSeries F) (X ^ m) • z := by
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finite (Submonoid.powers (X : F⟦X⟧)) z
  obtain ⟨m, hm⟩ := s.2
  choose w hw using hs
  refine ⟨m, w, funext fun j => ?_⟩
  rw [vecL, hw j, ← hm, Pi.smul_apply, smul_eq_mul, Algebra.smul_def]

theorem semilin_mem (θ : F⟦X⟧ →+* F⟦X⟧) (hθ : θ X ≠ 0) {M : Mx F⟦X⟧ a a} {M' : Mx F⟦X⟧ b b} {A A' : Mx F⟦X⟧ a b}
    (h : M * A'.map θ = A * M') {y : Fin a → F⟦X⟧} (hy : vecL y ∈ colL A') :
    vecL (M.mulVec fun j => θ (y j)) ∈ colL A := by
  obtain ⟨z, hz⟩ := hy
  obtain ⟨m, w, hw⟩ := exists_clear z
  have e1 : A'.mulVec w = (X : F⟦X⟧) ^ m • y := by
    apply vecL_injective
    rw [← linL_vecL, hw, map_smul, hz, vecL_smul]
  have e2 : (A'.map θ).mulVec (fun j => θ (w j)) = θ X ^ m • fun j => θ (y j) := by
    funext j
    have := RingHom.map_mulVec θ A' w j
    rw [e1] at this
    rw [show (fun j => θ (w j)) = θ ∘ w from rfl, ← this]
    simp
  have e3 : θ X ^ m • (M.mulVec fun j => θ (y j)) = A.mulVec (M'.mulVec fun j => θ (w j)) := by
    rw [Matrix.mulVec_mulVec, ← h, ← Matrix.mulVec_mulVec, e2, Matrix.mulVec_smul]
  have h0 : algebraMap F⟦X⟧ (LaurentSeries F) (θ X ^ m) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective F⟦X⟧ (LaurentSeries F))).2 (pow_ne_zero _ hθ)
  rw [← Submodule.smul_mem_iff _ h0, ← vecL_smul, e3, ← linL_vecL]
  exact LinearMap.mem_range_self _ _

theorem ker_eq_colL {C : Mx F⟦X⟧ 1 (a + 1)} {E : Mx F⟦X⟧ (a + 1) a} (h : C * E = 0) (hE : lrank E = a)
    (hC : lrank C = 1) : LinearMap.ker (linL C) = colL E := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨z, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← linL_mul, h]
    simp [linL]
  · have := LinearMap.finrank_range_add_finrank_ker (linL C)
    rw [← colL, finrank_colL, hC, Module.finrank_fin_fun] at this
    rw [finrank_colL, hE]
    omega

theorem exists_mulVec_eq_pow {C : Mx F⟦X⟧ 1 a} (hC : lrank C = 1) :
    ∃ (y : Fin a → F⟦X⟧) (m : ℕ), C.mulVec y = fun _ => X ^ m := by
  obtain ⟨z, hz⟩ : (fun _ => 1 : Fin 1 → LaurentSeries F) ∈ colL C := by
    rw [colL_eq_top hC]
    trivial
  obtain ⟨m, w, hw⟩ := exists_clear z
  refine ⟨w, m, vecL_injective ?_⟩
  rw [← linL_vecL, hw, map_smul, hz]
  funext j
  simp [vecL]

theorem line_rel (θ : F⟦X⟧ →+* F⟦X⟧) {M : Mx F⟦X⟧ a a} {M₂ : Mx F⟦X⟧ (a + 1) (a + 1)} {M₁ : Mx F⟦X⟧ 1 1}
    {B B' : Mx F⟦X⟧ a (a + 1)} {C C' : Mx F⟦X⟧ 1 (a + 1)} {E : Mx F⟦X⟧ (a + 1) a}
    (hB : M * B'.map θ = B * M₂) (hC : M₁ * C'.map θ = C * M₂) (h : C * E = 0) (hE : lrank E = a)
    (hC1 : lrank C = 1) {y y' : Fin (a + 1) → F⟦X⟧} {m m' : ℕ} (hy : C.mulVec y = fun _ => X ^ m)
    (hy' : C'.mulVec y' = fun _ => X ^ m') :
    algebraMap F⟦X⟧ (LaurentSeries F) X ^ m • vecL (M.mulVec fun j => θ (B'.mulVec y' j)) -
      (algebraMap F⟦X⟧ (LaurentSeries F) (θ X) ^ m' * algebraMap F⟦X⟧ (LaurentSeries F) (M₁ 0 0)) •
        vecL (B.mulVec y) ∈ colL (B * E) := by
  have e : ∀ {k : ℕ} (A : Mx F⟦X⟧ k (a + 1)), (fun j => θ (A.mulVec y' j)) = (A.map θ).mulVec fun j => θ (y' j) :=
    fun A => funext fun j => RingHom.map_mulVec θ A y' j
  let z : Fin (a + 1) → F⟦X⟧ := (X : F⟦X⟧) ^ m • (M₂.mulVec fun j => θ (y' j)) - (θ X ^ m' * M₁ 0 0) • y
  have hz : C.mulVec z = 0 := by
    simp only [z, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← hC]
    rw [← Matrix.mulVec_mulVec, ← e, hy, hy']
    funext j
    rw [Subsingleton.elim j 0]
    simp [Matrix.mulVec, dotProduct]
    ring
  have hk : vecL z ∈ colL E := by
    rw [← ker_eq_colL h hE hC1, LinearMap.mem_ker, linL_vecL, hz]
    funext j
    simp [vecL]
  obtain ⟨v, hv⟩ := hk
  refine ⟨v, ?_⟩
  rw [linL_mul, LinearMap.comp_apply, hv, linL_vecL]
  simp only [z, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← hB]
  rw [← Matrix.mulVec_mulVec, ← e, vecL_sub, vecL_smul, vecL_smul, map_pow, map_mul, map_pow]

theorem colL_eq_sup {B : Mx F⟦X⟧ a (a + 1)} {C : Mx F⟦X⟧ 1 (a + 1)} {E : Mx F⟦X⟧ (a + 1) a} (h : C * E = 0)
    (hE : lrank E = a) (hC1 : lrank C = 1) {y : Fin (a + 1) → F⟦X⟧} {m : ℕ} (hy : C.mulVec y = fun _ => X ^ m) :
    colL B = colL (B * E) ⊔ Submodule.span (LaurentSeries F) {vecL (B.mulVec y)} := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    have h0 : algebraMap F⟦X⟧ (LaurentSeries F) (X ^ m) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective F⟦X⟧ (LaurentSeries F))).2 (pow_ne_zero _ X_ne_zero)
    let s : LaurentSeries F := linL C z 0 / algebraMap F⟦X⟧ (LaurentSeries F) (X ^ m)
    have hk : z - s • vecL y ∈ colL E := by
      rw [← ker_eq_colL h hE hC1, LinearMap.mem_ker, map_sub, map_smul, linL_vecL, hy]
      funext j
      rw [Subsingleton.elim j 0, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, vecL, div_mul_cancel₀ _ h0, sub_self]
      rfl
    obtain ⟨v, hv⟩ := hk
    have : linL B z = linL (B * E) v + s • vecL (B.mulVec y) := by
      rw [linL_mul, LinearMap.comp_apply, hv, map_sub, map_smul, linL_vecL, sub_add_cancel]
    rw [this]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self _ _)
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  · refine sup_le (colL_mul_le _ _) ?_
    rw [Submodule.span_singleton_le_iff_mem, ← linL_vecL]
    exact LinearMap.mem_range_self _ _

end Columns

theorem filtration_of_chain {F : Type} [Field F] {ι : Type} (σ : Equiv.Perm ι) {l n t R : ℕ} (hl : 0 < l) (un : F⟦X⟧)
    (P D : ι → Mx F⟦X⟧ n n) (Pψ Dψ : Fin t → ι → Mx F⟦X⟧ 1 1) (rs : Fin t → Fin R) (dim : Fin (R + 1) → ℕ)
    (y : ι → Slot F n t R) (h0 : dim 0 = 0) (hR : dim (Fin.last R) = n)
    (hs : ∀ s, dim (rs s).succ = dim (rs s).castSucc + 1)
    (hy : ∀ i, (y i).Chain (y (σ i)) l un (P i) (D i) (fun s => Pψ s i) (fun s => Dψ s i) rs dim) :
    ∃ (V : ι → Fin (R + 1) → Submodule (LaurentSeries F) (Fin n → LaurentSeries F))
      (e : ι → Fin t → Fin n → F⟦X⟧) (m : ι → Fin t → ℤ),
      (∀ i, V i 0 = ⊥ ∧ V i (Fin.last R) = ⊤ ∧ Monotone (V i)) ∧
      (∀ k i j, Module.finrank (LaurentSeries F) (V i k) = Module.finrank (LaurentSeries F) (V j k)) ∧
      (∀ i k v, vecL v ∈ V (σ i) k → vecL ((P i).mulVec fun a => frob0 l (v a)) ∈ V i k) ∧
      (∀ i k v, vecL v ∈ V i k → vecL ((1 + (X : F⟦X⟧) • D i).mulVec fun a => gam0 0 un (v a)) ∈ V i k) ∧
      (∀ i s, vecL (e i s) ∉ V i (rs s).castSucc ∧
        V i (rs s).succ = V i (rs s).castSucc ⊔ Submodule.span (LaurentSeries F) {vecL (e i s)}) ∧
      (∀ i s, (((X : F⟦X⟧) : LaurentSeries F) ^ m i s) • vecL ((P i).mulVec fun a => frob0 l (e (σ i) s a)) -
        (((X : F⟦X⟧) : LaurentSeries F) ^ ((l : ℤ) * m (σ i) s) * ((Pψ s i 0 0 : F⟦X⟧) : LaurentSeries F)) •
          vecL (e i s) ∈ V i (rs s).castSucc) ∧
      ∀ i s, (((X : F⟦X⟧) : LaurentSeries F) ^ m i s) •
          vecL ((1 + (X : F⟦X⟧) • D i).mulVec fun a => gam0 0 un (e i s a)) -
        (((gamSer 0 un : F⟦X⟧) : LaurentSeries F) ^ m i s *
          ((1 + X * Dψ s i 0 0 : F⟦X⟧) : LaurentSeries F)) • vecL (e i s) ∈ V i (rs s).castSucc := by
  have h1 : HasSubst (X ^ l : F⟦X⟧) := HasSubst.X_pow hl.ne'
  have h2 : HasSubst (gamSer 0 un) := HasSubst.of_constantCoeff_zero' (by simp [gamSer])
  obtain ⟨φ, hφ⟩ : ∃ φ : F⟦X⟧ →+* F⟦X⟧, ⇑φ = frob0 l := ⟨(substAlgHom h1 : F⟦X⟧ →ₐ[F] F⟦X⟧), coe_substAlgHom h1⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : F⟦X⟧ →+* F⟦X⟧, ⇑γ = gam0 0 un := ⟨(substAlgHom h2 : F⟦X⟧ →ₐ[F] F⟦X⟧), coe_substAlgHom h2⟩
  have hφX : φ X = X ^ l := by rw [hφ, frob0, subst_X h1]
  have hγX : γ X = gamSer 0 un := by rw [hγ, gam0, subst_X h2]
  have hγ0 : γ X ≠ 0 := by
    rw [hγX, gamSer]
    refine mul_ne_zero X_ne_zero fun h => ?_
    simpa using congrArg constantCoeff h
  choose w m hw using fun i s => exists_mulVec_eq_pow ((hy i).2.2 s).2.2.2.2.2.2.1
  have hsup : ∀ i s, colL ((y i).A (rs s).succ) =
      colL ((y i).A (rs s).castSucc) ⊔ Submodule.span (LaurentSeries F) {vecL (((y i).B s).mulVec (w i s))} := by
    intro i s
    obtain ⟨-, -, e1, e2, e3, e4, e5, e6⟩ := (hy i).2.2 s
    rw [← e1, ← colL_eq_sup e2 e4 e5 (hw i s), e3, colL_mul_eq _ e6]
  refine ⟨fun i k => colL ((y i).A k), fun i s => ((y i).B s).mulVec (w i s), fun i s => m i s,
    fun i => ⟨?_, colL_eq_top (((hy i).1 _).2.trans hR), ?_⟩, fun k i j => ?_, fun i k v hv => ?_, fun i k v hv => ?_,
    fun i s => ⟨fun hm => ?_, hsup i s⟩, fun i s => ?_, fun i s => ?_⟩
  · exact Submodule.finrank_eq_zero.1 ((finrank_colL _).trans (((hy i).1 _).2.trans h0))
  · refine Fin.monotone_iff_le_succ.2 fun k => ?_
    exact (congrArg colL ((hy i).2.1 k)).trans_le (colL_mul_le _ _)
  · rw [finrank_colL, finrank_colL, ((hy i).1 k).2, ((hy j).1 k).2]
  · rw [← hφ]
    exact semilin_mem φ (by rw [hφX]; exact pow_ne_zero _ X_ne_zero) (hφ ▸ ((hy i).1 k).1.1) hv
  · rw [← hγ]
    exact semilin_mem γ hγ0 (hγ ▸ ((hy i).1 k).1.2) hv
  · have e := hsup i s
    rw [sup_eq_left.2 ((Submodule.span_singleton_le_iff_mem _ _).2 hm)] at e
    have e' := finrank_colL ((y i).A (rs s).succ)
    rw [e, finrank_colL, ((hy i).1 _).2, ((hy i).1 _).2, hs] at e'
    omega
  · obtain ⟨b1, c1, e1, e2, -, e4, e5, -⟩ := (hy i).2.2 s
    have := line_rel φ (hφ ▸ b1.1) (hφ ▸ c1.1) e2 e4 e5 (hw i s) (hw (σ i) s)
    rw [e1, hφX, hφ, map_pow, ← pow_mul] at this
    rw [← Nat.cast_mul, zpow_natCast, zpow_natCast]
    exact this
  · obtain ⟨b1, c1, e1, e2, -, e4, e5, -⟩ := (hy i).2.2 s
    have := line_rel γ (hγ ▸ b1.2) (hγ ▸ c1.2) e2 e4 e5 (hw i s) (hw i s)
    rw [e1, hγX, hγ, Matrix.add_apply, Matrix.one_apply_eq, Matrix.smul_apply, smul_eq_mul] at this
    rw [zpow_natCast, zpow_natCast]
    exact this

end GlobalTheory.WachPlace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenInterEqSingletonOfNoGenerisation
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem GlobalTheory.exists_open_inter_eq_singleton_of_no_generisation :
    ∀ (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X] (T : Set X) (x : X), IsClosed T → IsClosed ({x} : Set X) → x ∈ T → (∀ z ∈ T, z ⤳ x → z = x) → ∃ U : X.Opens, x ∈ U ∧ ∀ y ∈ U, y ∈ T ↔ y = x := by
  intro X _ T x hT hx hxT hgen
  obtain ⟨S, hSf, hScl, hSirr, hTS⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hT
  let S' : Set (Set X) := {t | t ∈ S ∧ x ∉ t}
  have hS'f : S'.Finite := hSf.subset (fun t ht => ht.1)
  have hcl : IsClosed (⋃₀ S') := by
    rw [Set.sUnion_eq_biUnion]
    exact hS'f.isClosed_biUnion (fun t ht => hScl t ht.1)
  refine ⟨⟨(⋃₀ S')ᶜ, hcl.isOpen_compl⟩, ?_, ?_⟩
  · show x ∈ (⋃₀ S')ᶜ
    rintro ⟨t, ht, hxt⟩
    exact ht.2 hxt
  · intro y hy
    have hy' : y ∈ (⋃₀ S')ᶜ := hy
    constructor
    · intro hyT
      rw [hTS] at hyT
      obtain ⟨t, htS, hyt⟩ := hyT
      by_cases hxt : x ∈ t
      · have hirr := hSirr t htS
        have hclt := hScl t htS
        obtain ⟨η, hηg⟩ := QuasiSober.sober hirr hclt
        have hgp : closure ({η} : Set X) = t := hηg.def
        have hη : η ∈ t := by
          rw [← hgp]; exact subset_closure rfl
        have hηT : η ∈ T := by
          rw [hTS]; exact ⟨t, htS, hη⟩
        have hsp : η ⤳ x := by
          rw [specializes_iff_mem_closure, hgp]; exact hxt
        have heq := hgen _ hηT hsp
        rw [heq, hx.closure_eq] at hgp
        rw [← hgp] at hyt
        exact hyt
      · exact absurd (Set.mem_sUnion.mpr ⟨t, (⟨htS, hxt⟩ : t ∈ S'), hyt⟩) hy'
    · rintro rfl; exact hxT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointLocalRingClosedPointCentreOfPlace
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.FieldPair

theorem exists_locRing_closedPoint_centre : ∀ {κ' : Type} [Field κ'] [Algebra ℂ κ'] (F : Place (algebraMap ℂ κ')) (A : Subalgebra ℂ κ'),
    Algebra.Smooth ℂ A → A.toSubring ≤ F.ring.toSubring →
    (∀ f : κ', ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ f * b = a) →
    ∃ (B : Subring κ') (hB : IsLocModel (algebraMap ℂ κ') B), RatRes (algebraMap ℂ κ') B ∧
      A.toSubring ≤ B ∧ B ≤ F.ring.toSubring ∧
      ((algebraMap ℂ κ').codRestrict B hB.const_mem).FormallySmooth := by
  intro κ' _ _ F A hsm hAF hfrac
  haveI : IsFractionRing A κ' := IsFractionRing.of_field A κ' fun z => by
    obtain ⟨a, ha, b, hb, hb0, e⟩ := hfrac z
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, by simp [← e, hb0]⟩
  let ι : A →+* F.ring := (algebraMap A κ').codRestrict F.ring (fun x => hAF x.2)
  let q : Ideal A := (IsLocalRing.maximalIdeal F.ring).comap ι
  have hq : q ≠ ⊤ := by
    intro h
    have h1 : (1 : A) ∈ q := h ▸ Submodule.mem_top
    exact (IsLocalRing.mem_maximalIdeal _).1 (show ι 1 ∈ _ from h1) (by simp)
  obtain ⟨n, hn, hqn⟩ := Ideal.exists_le_maximal q hq
  have hinv : ∀ s ∈ n.primeCompl, ((s : A) : κ')⁻¹ ∈ F.ring := by
    intro s hs
    have hs' : ι s ∉ IsLocalRing.maximalIdeal F.ring := fun h => hs (hqn h)
    have hu : IsUnit (ι s) := by
      by_contra h
      exact hs' ((IsLocalRing.mem_maximalIdeal _).2 h)
    obtain ⟨u, hu⟩ := hu.exists_right_inv
    have e : ((s : A) : κ') * (u : κ') = 1 := congrArg Subtype.val hu
    rw [← eq_inv_of_mul_eq_one_right e]
    exact u.2
  have hle : n.primeCompl ≤ nonZeroDivisors A := n.primeCompl_le_nonZeroDivisors
  let B0 : Subalgebra A κ' := Localization.subalgebra.ofField κ' n.primeCompl hle
  haveI : IsLocalization.AtPrime B0 n := Localization.subalgebra.isLocalization_ofField κ' _ hle
  have hAB : A.toSubring ≤ B0.toSubring := fun x hx => B0.algebraMap_mem (⟨x, hx⟩ : A)
  have hc : ∀ a, algebraMap ℂ κ' a ∈ B0.toSubring := fun a => hAB (A.algebraMap_mem a)
  letI : Algebra ℂ B0 := ((algebraMap A B0).comp (algebraMap ℂ A)).toAlgebra
  haveI : IsScalarTower ℂ A B0 := IsScalarTower.of_algebraMap_eq' rfl
  have hloc : IsLocalRing B0 := IsLocalization.AtPrime.isLocalRing B0 n
  refine ⟨B0.toSubring, ⟨hc, hloc, ?_, ?_⟩, ?_, hAB, ?_, ?_⟩
  · show (algebraMap ℂ B0).EssFiniteType
    refine RingHom.EssFiniteType.comp ?_ ?_
    · exact RingHom.essFiniteType_algebraMap.2 inferInstance
    · exact RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization B0 n.primeCompl)
  · intro f
    obtain ⟨a, ha, b, hb, hb0, e⟩ := hfrac f
    exact ⟨a, hAB ha, b, hAB hb, hb0, e⟩
  · intro r hr
    let r' : B0 := ⟨r, hr⟩
    letI : Field (A ⧸ n) := Ideal.Quotient.field n
    haveI : Module.Finite ℂ (A ⧸ n) := finite_of_finite_type_of_isJacobsonRing ℂ (A ⧸ n)
    have hsurj : Function.Surjective (algebraMap ℂ (A ⧸ n)) :=
      IsAlgClosed.algebraMap_bijective_of_isIntegral.2
    let e := IsLocalization.AtPrime.equivQuotMaximalIdeal n B0
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (e.symm (Ideal.Quotient.mk _ r'))
    obtain ⟨a, ha⟩ := hsurj (Ideal.Quotient.mk n x)
    refine ⟨a, ?_⟩
    let z : B0 := algebraMap A B0 (algebraMap ℂ A a)
    have hz : Ideal.Quotient.mk (IsLocalRing.maximalIdeal B0) z = Ideal.Quotient.mk _ r' := by
      rw [← e.apply_symm_apply (Ideal.Quotient.mk _ r'), ← hx, ← ha]
      exact (IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk n B0 (algebraMap ℂ A a)).symm
    have hm : r' - z ∈ IsLocalRing.maximalIdeal B0 := Ideal.Quotient.eq.1 hz.symm
    have hnu := (nonUnit_iff (R := B0.toSubring) (r' - z)).2 ((IsLocalRing.mem_maximalIdeal _).1 hm)
    exact hnu
  · rintro x ⟨a, s, hs, rfl⟩
    exact F.ring.toSubring.mul_mem (hAF a.2) (hinv s hs)
  · show (algebraMap ℂ B0).FormallySmooth
    haveI : Algebra.FormallyEtale A B0 := Algebra.FormallyEtale.of_isLocalization n.primeCompl
    haveI : Algebra.FormallySmooth ℂ B0 := Algebra.FormallySmooth.comp ℂ A B0
    exact RingHom.formallySmooth_algebraMap.2 inferInstance

end GlobalTheory.FieldPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalBudgetsTwoPointInduction
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem exists_rat_budget_term (r : ℕ) (hr : 0 < r) (e : ℕ) (he : e ≠ 0) (c : ℝ) (hc : 0 < c) :
    ∃ q : ℚ, 0 < q ∧ (q : ℝ) < (2 : ℝ) ^ (1 / (e : ℝ)) * e / (r * c) ∧
      ∀ t : ℤ, c ^ e < (t : ℝ) / (r : ℝ) ^ e → 2 * (e : ℚ) ^ e < q ^ e * t := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have heR : (0 : ℝ) < e := by exact_mod_cast Nat.pos_of_ne_zero he
  have hapos : 0 < ((r : ℝ) * c) ^ e := by positivity
  obtain ⟨T, hT⟩ : ∃ T : ℤ, T = ⌊((r : ℝ) * c) ^ e⌋ + 1 := ⟨_, rfl⟩
  have hTa : ((r : ℝ) * c) ^ e < (T : ℝ) := by
    rw [hT]; push_cast; exact Int.lt_floor_add_one _
  have hTpos : (0 : ℝ) < T := hapos.trans hTa
  have hupos : 0 < (2 : ℝ) ^ (1 / (e : ℝ)) * e / (r * c) := by positivity
  have hue : ((2 : ℝ) ^ (1 / (e : ℝ)) * e / (r * c)) ^ e = 2 * (e : ℝ) ^ e / ((r : ℝ) * c) ^ e := by
    rw [div_pow, mul_pow, one_div, Real.rpow_inv_natCast_pow (by norm_num) he]
  have hv0 : 0 ≤ (2 * (e : ℝ) ^ e / T) ^ ((e : ℝ)⁻¹) := by positivity
  have hve : ((2 * (e : ℝ) ^ e / T) ^ ((e : ℝ)⁻¹)) ^ e = 2 * (e : ℝ) ^ e / T :=
    Real.rpow_inv_natCast_pow (by positivity) he
  have hvu : (2 * (e : ℝ) ^ e / T) ^ ((e : ℝ)⁻¹) < (2 : ℝ) ^ (1 / (e : ℝ)) * e / (r * c) := by
    rw [← pow_lt_pow_iff_left₀ hv0 hupos.le he, hve, hue]
    exact div_lt_div_of_pos_left (by positivity) hapos hTa
  obtain ⟨q, hvq, hqu⟩ := exists_rat_btwn hvu
  have hq0 : (0 : ℝ) < q := lt_of_le_of_lt hv0 hvq
  refine ⟨q, by exact_mod_cast hq0, hqu, ?_⟩
  intro t ht
  have hct : c ^ e * (r : ℝ) ^ e < t := (lt_div_iff₀ (by positivity)).1 ht
  have hat : ((r : ℝ) * c) ^ e < t := by
    calc ((r : ℝ) * c) ^ e = c ^ e * (r : ℝ) ^ e := by rw [mul_pow, mul_comm]
      _ < t := hct
  have hTt : (T : ℝ) ≤ t := by
    have h1 := Int.floor_lt.2 hat
    have : T ≤ t := by omega
    exact_mod_cast this
  have key : 2 * (e : ℝ) ^ e < (q : ℝ) ^ e * t := by
    have h1 := pow_lt_pow_left₀ hvq hv0 he
    rw [hve, div_lt_iff₀ hTpos] at h1
    calc 2 * (e : ℝ) ^ e < (q : ℝ) ^ e * T := h1
      _ ≤ (q : ℝ) ^ e * t := mul_le_mul_of_nonneg_left hTt (by positivity)
  exact_mod_cast key

theorem exists_rat_budgets : ∀ (n r : ℕ) (c : ℕ → ℝ), 0 < r → (∀ e ∈ Finset.Icc 1 n, 0 < c e) →
    ∑ e ∈ Finset.Icc 1 n, (2 : ℝ) ^ (1 / (e : ℝ)) * e / c e ≤ 1 →
    ∃ (h : ℕ → ℚ), (∀ e, 0 < h e) ∧ ∑ e ∈ Finset.Icc 1 n, h e < 1 / (r : ℚ) ∧
      ∀ e ∈ Finset.Icc 1 n, ∀ t : ℤ, c e ^ e < (t : ℝ) / (r : ℝ) ^ e →
        2 * (e : ℚ) ^ e < h e ^ e * t := by
  intro n r c hr hc hsum
  have hex : ∀ e, ∃ q : ℚ, 0 < q ∧ (e ∈ Finset.Icc 1 n →
      (q : ℝ) < (2 : ℝ) ^ (1 / (e : ℝ)) * e / (r * c e) ∧
      ∀ t : ℤ, c e ^ e < (t : ℝ) / (r : ℝ) ^ e → 2 * (e : ℚ) ^ e < q ^ e * t) := by
    intro e
    by_cases he : e ∈ Finset.Icc 1 n
    · have he0 : e ≠ 0 := by
        have := (Finset.mem_Icc.1 he).1
        omega
      obtain ⟨q, hq0, hqu, hqt⟩ := exists_rat_budget_term r hr e he0 (c e) (hc e he)
      exact ⟨q, hq0, fun _ => ⟨hqu, hqt⟩⟩
    · exact ⟨1, one_pos, fun h => absurd h he⟩
  choose h hpos hprop using hex
  refine ⟨h, hpos, ?_, fun e he => (hprop e he).2⟩
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hR : ∑ e ∈ Finset.Icc 1 n, (h e : ℝ) < 1 / (r : ℝ) := by
    rcases (Finset.Icc 1 n).eq_empty_or_nonempty with hE | hE
    · rw [hE, Finset.sum_empty]; positivity
    · calc ∑ e ∈ Finset.Icc 1 n, (h e : ℝ)
          < ∑ e ∈ Finset.Icc 1 n, (2 : ℝ) ^ (1 / (e : ℝ)) * e / (r * c e) :=
            Finset.sum_lt_sum_of_nonempty hE (fun e he => (hprop e he).1)
        _ = 1 / (r : ℝ) * ∑ e ∈ Finset.Icc 1 n, (2 : ℝ) ^ (1 / (e : ℝ)) * e / c e := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun e _ => by ring
        _ ≤ 1 / (r : ℝ) * 1 := mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = 1 / (r : ℝ) := mul_one _
  have hR' : ((∑ e ∈ Finset.Icc 1 n, h e : ℚ) : ℝ) < ((1 / (r : ℚ) : ℚ) : ℝ) := by
    push_cast; exact hR
  exact Rat.cast_lt.mp hR'

end GlobalTheory.PairStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRenormalizationRigidificationMultipleStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH
open GlobalTheory.Poinc.Tors
theorem _root_.GlobalTheory.T.exists_renormalization_rigidification_multiple : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (w₀ : W0 U), w₀.IsGen → ∀ ρ : LB.Gen (A.L.pull (eSec A.A)), ρ.IsGen → ∃ (ρ' : LB.Gen (A.L.pull (eSec A.A))) (c : FractionRing R), c ≠ 0 ∧ NormW U w₀ ρ' ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (N : ℕ) (x : TFK (R := R) F ⟶ A.A) (fr fr' : FrAt x), IsTorsFrame A ρ N x fr → fr'.IsGen → (∀ z J, Good A.L z J → (val fr' (𝟙 _) z J).val = @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z (algebraMap (FractionRing R) F c)) * (val fr (𝟙 _) z J).val) → IsTorsFrame A ρ' N x fr' := by
  first | exact @GlobalTheory.Poinc.Renorm.exists_renorm | exact GlobalTheory.Poinc.Renorm.exists_renorm | (intros; apply GlobalTheory.Poinc.Renorm.exists_renorm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescalePrimitiveInLatticeAtSplitPrimesStatement
section
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rescale_primitive_in_lattice_at_split_primes : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.IsLattice E → ∀ x y : Fin n → E, x ≠ 0 → y ≠ 0 →
    ∀ (P : Finset (HeightOneSpectrum (𝓞 F))) (τ : ∀ v : P, E →ₐ[F] Fv F v.1), ∃ c : E, c ≠ 0 ∧
      ∀ v : P, PrimAt (GlobalTheory.AdelicU.splitPrime (τ v)) L (c • x) ∧ PrimAt (GlobalTheory.AdelicU.splitPrime (τ v)) L ((σ c)⁻¹ • y) := by
  first | exact @GlobalTheory.PlaneSkewScale.exists_rescale_primAt | exact GlobalTheory.PlaneSkewScale.exists_rescale_primAt | (intros; apply GlobalTheory.PlaneSkewScale.exists_rescale_primAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionTorusAndAbelianQuotientStatement
section
open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringAction_torus_and_abelian_quotient : ∀ (O : Type) [CommRing O] (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G] (act : OAct O G), IsSemiAbelian G → ∀ (T : TorusExtension G), letI := T.addCommGroup; letI := T.grpB; ∃ (actB : OAct O T.B) (actT : OAct O (splitTorus (Sp k) T.X)), (∀ a, T.q ≫ actB.act a = act.act a ≫ T.q) ∧ (∀ a, actT.act a ≫ T.i = T.i ≫ act.act a) := by
  first | exact @GlobalTheory.SemiAbAct.exists_torus_quotient_act | exact GlobalTheory.SemiAbAct.exists_torus_quotient_act | (intros; apply GlobalTheory.SemiAbAct.exists_torus_quotient_act <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearActionDualWeylTensorStatement
section
open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semilinear_action_dualWeylTensor : ∀ (R : Type) [CommRing R] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (mu : ι → ℕ → ℕ) (g : R ≃+* R), ∃ Φ : NablaT R N mu →+ NablaT R N mu, Function.Injective Φ ∧ (∀ (c : R) x, Φ (c • x) = g c • Φ x) ∧ ∀ (h : ι → GL (Fin N) R), (∀ τ a b, g ((h τ : Matrix (Fin N) (Fin N) R) a b) = (h τ : Matrix (Fin N) (Fin N) R) a b) → ∀ x, Φ (grp R N mu h x) = grp R N mu h (Φ x) := by
  first | exact @GlobalTheory.semilinear_transport | exact GlobalTheory.semilinear_transport | (intros; apply GlobalTheory.semilinear_transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothPartitionOfUnityComplexPointsStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_partition_of_unity_complexPoints : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} (W : CxPts X.str σ → Set (CxPts X.str σ)), (∀ y, W y ∈ 𝓝 y) → ∃ (s : Finset (CxPts X.str σ)) (ρ : s → CxPts X.str σ → ℝ), (∀ i y, CInfAt (ρ i) y) ∧ (∀ i, tsupport (ρ i) ⊆ W i) ∧ ∀ y, ∑ i, ρ i y = 1 := by
  first | exact @GlobalTheory.GoodTop.exists_cInf_partition | exact GlobalTheory.GoodTop.exists_cInf_partition | (intros; apply GlobalTheory.GoodTop.exists_cInf_partition <;> assumption)
end

