import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0024
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0035

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NotField
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.CoordExist

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

noncomputable def linL (H : HermSp M V) (y : V) : V →ₗ[E] E where
  toFun x := H.h x y
  map_add' a b := H.h_add_left a b y
  map_smul' a x := H.h_smul_left a x y

lemma h_sum_left (H : HermSp M V) {n : ℕ} (c : Fin n → E) (b : Fin n → V) (y : V) :
    H.h (∑ i, c i • b i) y = ∑ i, c i * H.h (b i) y := by
  show linL H y (∑ i, c i • b i) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul]
  rfl

lemma hf_eq (H : HermSp M V) {n : ℕ} (b : Fin n → V) (c d : Fin n → E) :
    hf M.L (Matrix.of fun i j => H.h (b i) (b j)) c d = H.h (∑ i, c i • b i) (∑ j, d j • b j) := by

  have hr : ∀ (x : V) (d : Fin n → E), H.h x (∑ j, d j • b j) = ∑ j, M.L.cj (d j) * H.h x (b j) := by
    intro x d
    rw [H.h_herm, h_sum_left, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, ← H.h_herm]
  rw [h_sum_left]
  unfold GlobalTheory.HL.hf
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hr, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.of_apply]
  ring

lemma hf_basis (H : HermSp M V) {n : ℕ} (b : Module.Basis (Fin n) E V) (x y : V) :
    hf M.L (Matrix.of fun i j => H.h (b i) (b j)) (b.equivFun x) (b.equivFun y) = H.h x y := by
  rw [hf_eq, b.sum_equivFun, b.sum_equivFun]

lemma nontriv (L : LocE F E) : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; norm_num)

lemma hermND (H : HermSp M V) {n : ℕ} (b : Module.Basis (Fin n) E V) :
    IsHermND M.L (Matrix.of fun i j => H.h (b i) (b j)) := by
  refine ⟨?_, ?_⟩
  · unfold GlobalTheory.HL.IsHerm GlobalTheory.HL.cT
    ext i j
    exact (H.h_herm (b j) (b i)).symm
  · have := M.L.free
    have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [M.L.rank]; norm_num)
    set G : Matrix (Fin n) (Fin n) E := Matrix.of fun i j => H.h (b i) (b j) with hGdef
    have hvec : ∀ (v : Fin n → E) j, (Matrix.vecMul v G) j = H.h (∑ i, v i • b i) (b j) := by
      intro v j
      rw [h_sum_left]
      simp only [Matrix.vecMul, dotProduct, hGdef, Matrix.of_apply]
    have hright : ∀ x y : V, H.h x y = ∑ j, M.L.cj (b.repr y j) * H.h x (b j) := by
      intro x y
      conv_lhs => rw [← b.sum_repr y]
      rw [H.h_herm, h_sum_left, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, ← H.h_herm]

    have hinj : Function.Injective (Matrix.vecMulLinear G) := by
      intro v v' hvv
      have hvv' : Matrix.vecMul v G = Matrix.vecMul v' G := hvv
      have hd : ∀ j, (Matrix.vecMul (v - v') G) j = 0 := by
        intro j
        rw [Matrix.sub_vecMul, hvv', sub_self]
        rfl
      have hx : ∑ i, (v - v') i • b i = 0 := by
        apply H.nondeg
        intro y
        rw [hright]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [← hvec, hd, mul_zero]
      have h0 := Fintype.linearIndependent_iff.mp b.linearIndependent (v - v') hx
      funext i
      exact sub_eq_zero.mp (h0 i)

    have hsurj : Function.Surjective (Matrix.vecMulLinear G) := by
      have h2 : Function.Injective ((Matrix.vecMulLinear G).restrictScalars F) := hinj
      exact LinearMap.injective_iff_surjective.mp h2
    exact (Matrix.isUnit_iff_isUnit_det G).mp (Matrix.vecMul_surjective_iff_isUnit.mp hsurj)

lemma not_field (L : LocE F E) (g : SplitG L) : ¬ IsField E := by
  intro hE
  have hx : g.e.symm (1, 0) ≠ 0 := by
    intro h0
    have h1 := congrArg g.e h0
    simp at h1
  obtain ⟨x', hx'⟩ := hE.mul_inv_cancel hx
  have hxy : g.e.symm (1, 0) * g.e.symm (0, 1) = 0 := by
    rw [← map_mul]
    simp
  have hy : g.e.symm (0, 1) = 0 := by
    calc g.e.symm (0, 1) = (x' * g.e.symm (1, 0)) * g.e.symm (0, 1) := by
          rw [mul_comm x', hx', one_mul]
      _ = 0 := by rw [mul_assoc, hxy, mul_zero]
  have h1 := congrArg g.e hy
  simp at h1

lemma gram_eq {H : HermSp M V} {r : ℕ} (A : LocNG.FrameD H r) (a b : Fin (r + 1)) :
    H.h (A.f a) (A.f b) = if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E A.T else 0 := by
  split_ifs with hab
  · rw [hab.1, hab.2]
    exact A.h_zz
  · exact A.h_iso a b (not_and_or.mp hab)

lemma dual_eq {H : HermSp M V} {r : ℕ} (A : LocNG.FrameD H r) (a : Fin (r + 1)) (j : Fin r) :
    H.h (A.f a) (A.es j) = if a = j.castSucc then 1 else 0 := by
  induction a using Fin.lastCases with
  | last =>
    rw [if_neg (Fin.castSucc_lt_last j).ne', H.h_herm, A.h_sz, map_zero]
  | cast i =>
    rw [A.h_es i j]
    simp only [Fin.castSucc_inj]

lemma unit_of {T : F} (hT : T ∈ 𝒪[F]) (u : 𝒪[F]) (h : (u : F) * T = 1) :
    ∃ v : (𝒪[F])ˣ, ((v : 𝒪[F]) : F) = T := by
  refine ⟨⟨⟨T, hT⟩, u, ?_, ?_⟩, rfl⟩
  · apply Subtype.ext
    show T * (u : F) = 1
    rw [mul_comm]
    exact h
  · apply Subtype.ext
    show (u : F) * T = 1
    exact h

end

theorem exists_coord : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∃ S : Frames M.L r k, Nonempty (Coord P S) := by
  intro F _ _ _ E _ _ _ _ M hOK V _ _ H r k P hrank hrel
  have := hOK.loc
  have : Nontrivial E := nontriv M.L
  have := H.free
  have := H.fin
  unfold LocNG.FPair.RelG LocNG.FPair.IsPoint LocNG.FPair.NormsOK at hrel
  obtain ⟨-, -, hG, -, -, ⟨w, hw⟩, hAT, hA0, hBT, hB0, hsp⟩ := hrel

  obtain ⟨ϖ, hϖ, hϖs⟩ : ∃ ϖ : 𝒪[F], Irreducible ϖ ∧ ∀ g, M.split = some g → ϖ = g.q := by
    cases hs : M.split with
    | none =>
      obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
      exact ⟨ϖ, hϖ, fun g hg => by cases hg⟩
    | some g =>
      exact ⟨g.q, g.q_irr, fun g' hg => by cases hg; rfl⟩
  let bs : Module.Basis (Fin (k + 2 * r + 1)) E V := Module.finBasisOfFinrankEq E V hrank
  have hZ : (Matrix.of fun a c => hf M.L (Matrix.of fun i j => H.h (bs i) (bs j))
      (bs.equivFun (P.B.f c)) (bs.equivFun (P.A.f a))) = H.Zhat P.A.f P.B.f := by
    ext a c
    simp only [Matrix.of_apply, hf_basis]
    rfl
  have hD1 : lead (H.Zhat P.A.f P.B.f) (Fin.last (r + 1)) = H.Dl P.A.f P.B.f (r + 1) := by
    unfold GlobalTheory.HL.lead HermSp.Dl
    rw [dif_pos le_rfl]
  have hD0 : lead (H.Zhat P.A.f P.B.f) (Fin.last r).castSucc = H.Dl P.A.f P.B.f r := by
    unfold GlobalTheory.HL.lead HermSp.Dl
    rw [dif_pos (Nat.le_succ r)]
  have hG' := hG
  unfold LocNG.FPair.Gv HermSp.Gdet HermSp.normE at hG'
  rw [← hD1, ← hD0, ← hZ] at hG'
  let S : Frames M.L r k :=
    { ϖ := ϖ
      ϖ_irr := hϖ
      Hm := Matrix.of fun i j => H.h (bs i) (bs j)
      herm := hermND H bs
      T := Units.mk0 P.A.T hA0
      T' := Units.mk0 P.B.T hB0
      f := fun a => bs.equivFun (P.A.f a)
      f' := fun a => bs.equivFun (P.B.f a)
      es := fun j => bs.equivFun (P.A.es j)
      es' := fun j => bs.equivFun (P.B.es j)
      gram := fun a c => by
        rw [hf_basis, gram_eq]
        rfl
      gram' := fun a c => by
        rw [hf_basis, gram_eq]
        rfl
      dual := fun a j => by rw [hf_basis, dual_eq]
      dual' := fun a j => by rw [hf_basis, dual_eq]
      iso := fun i j => by rw [hf_basis, P.A.h_ss]
      iso' := fun i j => by rw [hf_basis, P.B.h_ss]
      w := w
      relevant := fun a c => by
        rw [hf_basis, ← hw a c]
        have hsq : ((-1 : E) ^ (r - (c : ℕ))) * (-1) ^ (r - (c : ℕ)) = 1 := by
          rw [← mul_pow]
          simp
        show H.h (P.B.f c) (P.A.f a) =
          (-1) ^ (r - (c : ℕ)) * H.h (P.B.f c) (P.A.f a) * (-1) ^ (r - (c : ℕ))
        linear_combination (-(H.h (P.B.f c) (P.A.f a))) * hsq
      G_ne := hG'
      gg := M.split.isSome
      gg_ok := by
        intro hgg
        obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp hgg
        obtain ⟨⟨u, v, hu, hv⟩, -⟩ := hsp g hg
        exact ⟨not_field M.L g, unit_of hAT u hu, unit_of hBT v hv⟩ }
  refine ⟨S, ⟨{ e := bs.equivFun
                h_eq := fun x y => hf_basis H bs x y
                f_eq := fun a => rfl
                f'_eq := fun a => rfl
                es_eq := fun a => rfl
                es'_eq := fun a => rfl
                T_eq := rfl
                T'_eq := rfl
                gg_none := fun h => ?_
                gg_some := fun g hg => ⟨?_, hϖs g hg⟩ }⟩⟩
  · show M.split.isSome = false
    rw [h]
    rfl
  · show M.split.isSome = true
    rw [hg]
    rfl

end GlobalTheory.HL.CoordExist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitMassEquivariantConstantFibre
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.MassFibre

theorem card_mul_relIndex {G : Type} [Group G] (H K : Subgroup G) (hle : H ≤ K) :
    Nat.card H * H.relIndex K = Nat.card K := by
  have h1 := Subgroup.card_mul_index (H.subgroupOf K)
  have h2 : Nat.card (H.subgroupOf K) = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [h2] at h1
  exact h1

theorem encard_coe_subgroup {G : Type} [Group G] (H : Subgroup G) :
    ((H : Set G).encard : ℝ≥0∞) = if Nat.card H = 0 then ⊤ else (Nat.card H : ℝ≥0∞) := by
  split_ifs with h
  · have : (H : Set G).Infinite := by
      rcases Nat.card_eq_zero.mp h with h' | h'
      · exact absurd h' (not_isEmpty_of_nonempty _)
      · exact Set.infinite_coe_iff.mp h'
    rw [Set.encard_eq_top_iff.mpr this]; rfl
  · have hf : (H : Set G).Finite := by
      have := Nat.finite_of_card_ne_zero h
      exact Set.toFinite _
    rw [← hf.cast_ncard_eq, ← Nat.card_coe_set_eq]
    rfl

theorem inv_encard_eq_relIndex_mul {G : Type} [Group G] (H K : Subgroup G) (hle : H ≤ K)
    (hr : H.relIndex K ≠ 0) :
    (((H : Set G).encard : ℝ≥0∞))⁻¹ = (H.relIndex K : ℝ≥0∞) * (((K : Set G).encard : ℝ≥0∞))⁻¹ := by
  have hc := card_mul_relIndex H K hle
  rw [encard_coe_subgroup, encard_coe_subgroup]
  by_cases hK : Nat.card K = 0
  · have hH : Nat.card H = 0 := by
      rw [hK] at hc
      rcases Nat.mul_eq_zero.mp hc with h | h
      · exact h
      · exact absurd h hr
    simp [hH, hK]
  · have hH : Nat.card H ≠ 0 := by
      intro h; rw [h, zero_mul] at hc; exact hK hc.symm
    rw [if_neg hH, if_neg hK, ← hc]
    push_cast
    rw [ENNReal.mul_inv (Or.inl (by exact_mod_cast hH)) (Or.inl (by simp)), mul_comm,
      mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast hr) (by simp), mul_one]

end GlobalTheory.MassFibre

namespace GlobalTheory.MassFibre

open MulAction

noncomputable def wt {G : Type} [Group G] (Γ : Subgroup G) {Y : Type} [MulAction G Y] (y : Y) : ℝ≥0∞ :=
  ((((Γ ⊓ MulAction.stabilizer G y : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹

theorem wt_smul {G : Type} [Group G] (Γ : Subgroup G) {Y : Type} [MulAction G Y] (γ : G)
    (hγ : γ ∈ Γ) (y : Y) : wt Γ (γ • y) = wt Γ y := by
  unfold wt
  congr 2
  have hset : ((Γ ⊓ MulAction.stabilizer G (γ • y) : Subgroup G) : Set G)
      = (fun h => γ * h * γ⁻¹) '' ((Γ ⊓ MulAction.stabilizer G y : Subgroup G) : Set G) := by
    ext x
    simp only [Subgroup.coe_inf, Set.mem_inter_iff, SetLike.mem_coe, MulAction.mem_stabilizer_iff,
      Set.mem_image]
    constructor
    · rintro ⟨hx1, hx2⟩
      refine ⟨γ⁻¹ * x * γ, ⟨?_, ?_⟩, by group⟩
      · exact Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hγ) hx1) hγ
      · rw [mul_smul, mul_smul, hx2, inv_smul_smul]
    · rintro ⟨h, ⟨hh1, hh2⟩, rfl⟩
      refine ⟨Γ.mul_mem (Γ.mul_mem hγ hh1) (Γ.inv_mem hγ), ?_⟩
      rw [mul_smul, mul_smul, inv_smul_smul, hh2]
  rw [hset, Function.Injective.encard_image]
  intro a b hab
  simpa using hab

theorem wt_of_mem_orbit {G : Type} [Group G] (Γ : Subgroup G) {Y : Type} [MulAction G Y]
    {y y' : Y} (h : y' ∈ MulAction.orbit Γ y) : wt Γ y' = wt Γ y := by
  obtain ⟨γ, rfl⟩ := h
  show wt Γ (γ • y) = wt Γ y
  rw [Subgroup.smul_def]
  exact wt_smul Γ γ γ.2 y

theorem wt_out_mk {G : Type} [Group G] (Γ : Subgroup G) {Y : Type} [MulAction G Y] (y : Y) :
    wt Γ (Quotient.out (Quotient.mk (MulAction.orbitRel Γ Y) y : MulAction.orbitRel.Quotient Γ Y)) = wt Γ y :=
  wt_of_mem_orbit Γ (Quotient.mk_out (s := MulAction.orbitRel Γ Y) y)

end GlobalTheory.MassFibre

namespace GlobalTheory.MassFibre

theorem fibre_sum {G : Type} [Group G] (Γ : Subgroup G) {Y Z : Type} [MulAction G Y] [MulAction G Z]
    (f : Y → Z) (S : Set Z) (n : ℕ) (hf : ∀ (g : G) (y : Y), f (g • y) = g • f y)
    (hfin : ∀ z ∈ S, Finite {y // f y = z} ∧ Nat.card {y // f y = z} = n)
    (hemp : ∀ z, z ∉ S → IsEmpty {y // f y = z})
    (fbar : MulAction.orbitRel.Quotient Γ Y → MulAction.orbitRel.Quotient Γ Z)
    (hfbar : ∀ y, fbar (Quotient.mk _ y) = Quotient.mk _ (f y))
    (O : MulAction.orbitRel.Quotient Γ Z) :
    ∑' P : {P // fbar P = O}, wt Γ (Quotient.out P.1) = (n : ℝ≥0∞) * (if Quotient.out O ∈ S then wt Γ (Quotient.out O) else 0) := by

  classical
  by_cases hz : Quotient.out O ∈ S
  swap
  · rw [if_neg hz, mul_zero]
    haveI : IsEmpty {P // fbar P = O} := by
      refine ⟨fun ⟨P, hP⟩ => ?_⟩
      have h1 : Quotient.mk (MulAction.orbitRel Γ Z) (f (Quotient.out P))
          = Quotient.mk (MulAction.orbitRel Γ Z) (Quotient.out O) := by
        rw [← hfbar, Quotient.out_eq, Quotient.out_eq, hP]
      obtain ⟨γ, hγ⟩ := Quotient.exact h1
      exact (hemp _ hz).false ⟨(γ⁻¹ : G) • Quotient.out P, by
        rw [hf, ← hγ]; simp [Subgroup.smul_def]⟩
    simp
  rw [if_pos hz]
  obtain ⟨z, hzO⟩ : ∃ z, Quotient.out O = z := ⟨_, rfl⟩
  rw [hzO] at hz ⊢
  have hOz : Quotient.mk (MulAction.orbitRel Γ Z) z = O := by rw [← hzO, Quotient.out_eq]
  let Δ : Subgroup G := Γ ⊓ MulAction.stabilizer G z
  have hΔ : ∀ {g : G}, g ∈ Δ ↔ g ∈ Γ ∧ g • z = z := fun {g} => by
    simp [Δ, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
  let p : SubMulAction Δ Y :=
    { carrier := f ⁻¹' {z}
      smul_mem' := fun δ y hy => by
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy ⊢
        rw [Subgroup.smul_def, hf, hy]; exact (hΔ.mp δ.2).2 }
  have hmem : ∀ y : Y, y ∈ p ↔ f y = z := fun y => Iff.rfl
  let e : p ≃ {y // f y = z} := Equiv.subtypeEquivRight hmem
  haveI : Finite {y // f y = z} := (hfin z hz).1
  haveI : Finite p := Finite.of_equiv _ e.symm
  have hcard : Nat.card p = n := (Nat.card_congr e).trans (hfin z hz).2

  let φ : MulAction.orbitRel.Quotient Δ p → {P // fbar P = O} := fun Q =>
    ⟨Quotient.mk _ (Quotient.out Q : p).1, by
      rw [hfbar, (hmem _).mp (Quotient.out Q).2, hOz]⟩
  have hinj : Function.Injective φ := by
    intro Q1 Q2 h
    have h' := congrArg Subtype.val h
    obtain ⟨γ, hγ⟩ := Quotient.exact h'
    have hγΔ : (γ : G) ∈ Δ := by
      refine hΔ.mpr ⟨γ.2, ?_⟩
      have hy1 := (hmem _).mp (Quotient.out Q1).2
      have hy2 := (hmem _).mp (Quotient.out Q2).2
      calc (γ : G) • z = (γ : G) • f (Quotient.out Q2 : p).1 := by rw [hy2]
        _ = f ((γ : G) • (Quotient.out Q2 : p).1) := (hf _ _).symm
        _ = f (Quotient.out Q1 : p).1 := by rw [← hγ]; rfl
        _ = z := hy1
    rw [← Quotient.out_equiv_out]
    refine ⟨⟨γ, hγΔ⟩, ?_⟩
    apply Subtype.ext
    exact hγ
  have hsurj : Function.Surjective φ := by
    rintro ⟨P, hP⟩
    have h1 : Quotient.mk (MulAction.orbitRel Γ Z) (f (Quotient.out P))
        = Quotient.mk (MulAction.orbitRel Γ Z) z := by
      rw [← hfbar, Quotient.out_eq, hP, hOz]
    obtain ⟨γ, hγ⟩ := Quotient.exact h1
    let y' : p := ⟨(γ⁻¹ : G) • Quotient.out P, by
      rw [hmem, hf, ← hγ]; simp [Subgroup.smul_def]⟩
    refine ⟨Quotient.mk _ y', Subtype.ext ?_⟩
    obtain ⟨δ, hδ⟩ := (Quotient.mk_out (s := MulAction.orbitRel Δ p) y')
    show Quotient.mk _ _ = P
    conv_rhs => rw [← Quotient.out_eq P]
    apply Quotient.sound
    refine ⟨⟨(δ : G) * (γ : G)⁻¹, Γ.mul_mem (hΔ.mp δ.2).1 (Γ.inv_mem γ.2)⟩, ?_⟩
    rw [← hδ]
    show ((δ : G) * (γ : G)⁻¹) • Quotient.out P = (δ : G) • ((γ⁻¹ : G) • Quotient.out P)
    rw [mul_smul]

  have hw : ∀ y : p, wt Γ (y : Y) = ((MulAction.orbit Δ y).ncard : ℝ≥0∞) * wt Γ z := by
    intro y
    have hy := (hmem _).mp y.2
    have hle : (Γ ⊓ MulAction.stabilizer G (y : Y) : Subgroup G) ≤ Δ := by
      intro g hg
      rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff] at hg
      refine hΔ.mpr ⟨hg.1, ?_⟩
      rw [← hy, ← hf, hg.2]
    have hsub : (Γ ⊓ MulAction.stabilizer G (y : Y) : Subgroup G).subgroupOf Δ
        = MulAction.stabilizer Δ y := by
      ext δ
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff,
        MulAction.mem_stabilizer_iff]
      constructor
      · rintro ⟨-, h⟩; exact Subtype.ext h
      · intro h; exact ⟨(hΔ.mp δ.2).1, congrArg Subtype.val h⟩
    have hri : (Γ ⊓ MulAction.stabilizer G (y : Y) : Subgroup G).relIndex Δ
        = (MulAction.orbit Δ y).ncard := by
      rw [Subgroup.relIndex, hsub, MulAction.index_stabilizer]
    have hne : (MulAction.orbit Δ y).ncard ≠ 0 :=
      (Set.ncard_pos (Set.toFinite _)).mpr ⟨y, MulAction.mem_orbit_self y⟩ |>.ne'
    unfold wt
    rw [inv_encard_eq_relIndex_mul _ _ hle (hri ▸ hne), hri]
  rw [← (Equiv.ofBijective φ ⟨hinj, hsurj⟩).tsum_eq]
  haveI : Fintype (MulAction.orbitRel.Quotient Δ p) := Fintype.ofFinite _
  rw [tsum_fintype]
  have hterm : ∀ Q : MulAction.orbitRel.Quotient Δ p,
      wt Γ (Quotient.out (Equiv.ofBijective φ ⟨hinj, hsurj⟩ Q).1)
        = ((MulAction.orbit Δ (Quotient.out Q)).ncard : ℝ≥0∞) * wt Γ z := by
    intro Q
    rw [← hw]
    exact wt_out_mk Γ _
  simp_rw [hterm, ← Finset.sum_mul]
  congr 1
  have hsum : ∑ Q : MulAction.orbitRel.Quotient Δ p, (MulAction.orbit Δ (Quotient.out Q)).ncard = n := by
    rw [← hcard, Nat.card_congr (MulAction.selfEquivSigmaOrbits Δ p), Nat.card_sigma]
    refine Finset.sum_congr rfl (fun Q _ => ?_)
    rw [Nat.card_coe_set_eq]
  rw [← hsum]
  push_cast
  rfl

theorem mass_fibre : ∀ {G : Type} [Group G] (Γ : Subgroup G) (Y Z : Type) [MulAction G Y] [MulAction G Z] (f : Y → Z) (S : Set Z) (n : ℕ), (∀ (g : G) (y : Y), f (g • y) = g • f y) → (∀ (g : G) (z : Z), z ∈ S → g • z ∈ S) → (∀ z ∈ S, Finite {y // f y = z} ∧ Nat.card {y // f y = z} = n) → (∀ z, z ∉ S → IsEmpty {y // f y = z}) → (∑' o : MulAction.orbitRel.Quotient Γ Y, ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹) = (n : ℝ≥0∞) * ∑' o : MulAction.orbitRel.Quotient Γ Z, if o.out ∈ S then ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹ else 0 := by
  intro G _ Γ Y Z _ _ f S n hf hS hfin hemp
  let fbar : MulAction.orbitRel.Quotient Γ Y → MulAction.orbitRel.Quotient Γ Z :=
    Quotient.map' f (fun a b h => by
      obtain ⟨γ, hγ⟩ := h
      refine ⟨γ, ?_⟩
      show (γ : G) • f b = f a
      rw [← hf, ← hγ]; rfl)
  have hfbar : ∀ y, fbar (Quotient.mk _ y) = Quotient.mk _ (f y) := fun y => rfl
  have key := fibre_sum Γ f S n hf hfin hemp fbar hfbar
  change ∑' o : MulAction.orbitRel.Quotient Γ Y, wt Γ (Quotient.out o) = _
  rw [← (Equiv.sigmaFiberEquiv fbar).tsum_eq, ENNReal.tsum_sigma', ← ENNReal.tsum_mul_left]
  refine tsum_congr (fun O => ?_)
  exact key O

end GlobalTheory.MassFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StMatSpec
section
open NumberField GlobalTheory.HL
open scoped Classical

noncomputable section

namespace GlobalTheory.HL.TraceConjugationCover

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  {A : Places F E sig} {r k : ℕ}

def stMat (G : GFrames A r k) (x : G.GLV) : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  if h : ∃ B : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ∀ b, x (G.f' b) = ∑ a, B a b • G.f' a then h.choose else 0

theorem stMat_spec (G : GFrames A r k) (x : G.GLV)
    (h : ∃ B : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ∀ b, x (G.f' b) = ∑ a, B a b • G.f' a) :
    ∀ b, x (G.f' b) = ∑ a, stMat G x a b • G.f' a := by
  unfold stMat; rw [dif_pos h]; exact h.choose_spec

end GlobalTheory.HL.TraceConjugationCover

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentStabilizesSomeLatticeStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_stabilizes_some_lattice : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (g : ((Fin n → E) ≃ₗ[E] (Fin n → E))) (e : ℕ), (((g : (Fin n → E) →ₗ[E] (Fin n → E)) - 1) ^ e = 0) → ∃ Λ : Submodule L.O (Fin n → E), IsLat L Λ ∧ g ∈ stabL L Λ := by
  first | exact @GlobalTheory.HL.exists_isLat_stabL_of_unipotent | exact GlobalTheory.HL.exists_isLat_stabL_of_unipotent | (intros; apply GlobalTheory.HL.exists_isLat_stabL_of_unipotent <;> assumption)
end

