import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp
import Formalism.LocalToGlobal.Columns.RecLevelTop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0442
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CongruenceLevelEqDepthSucc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricFlagBasisVectorEqSingleOfNoExtra
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0231
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0128
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0472
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStepLevelConjBaseLatticeUnitary
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.ChEx

theorem exists_stepLevel_conj : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E σ J T f bad) (b : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), b ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) → (∀ v, bc (prV (E := E) v) b ∈ levelVL σ J v S.Lb) → (∀ v, (T : 𝓞 F) ∈ v.asIdeal → (S.Uloc v).map (MulAut.conj (bc (prV (E := E) v) b)).toMonoidHom = S.Uloc v) → (∀ v, v ∉ bad → (T : 𝓞 F) ∉ v.asIdeal → bc (prV (E := E) v) b = 1) → ∃ S' : StepLevel F E σ J T f bad, S'.Lb = S.Lb ∧ S'.U = S.U.map (MulAut.conj b).toMonoidHom ∧ ∀ (x : S'.U) (z : S.U), x.1 = b * z.1 * b⁻¹ → S'.chi x = S.chi z := by
  intro F E _ _ _ _ _ σ n J T f bad S b hb hlev hT hone
  classical
  let eqv := Subgroup.equivMapOfInjective S.U (MulAut.conj b).toMonoidHom
    (fun x y h => (MulAut.conj b).injective h)
  have heqv : ∀ z : S.U, ((eqv z : S.U.map (MulAut.conj b).toMonoidHom) : GL (Fin n) _) = b * z.1 * b⁻¹ := fun z => rfl
  have hbc : ∀ v (x : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), bc (prV (E := E) v) (b⁻¹ * x * b) =
      (bc (prV (E := E) v) b)⁻¹ * bc (prV (E := E) v) x * bc (prV (E := E) v) b := fun v x => by
    rw [map_mul, map_mul, map_inv]
  have hP : ∀ x, b⁻¹ * x * b ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) ↔ x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) := fun x => by
    constructor
    · intro h
      have e2 : b * (b⁻¹ * x * b) * b⁻¹ = x := by group
      rw [← e2]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hb h) (Subgroup.inv_mem _ hb)
    · intro h
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hb) h) hb
  let S' : StepLevel F E σ J T f bad :=
    { Lb := S.Lb
      Lb_fin := S.Lb_fin
      Lb_span := S.Lb_span
      Lb_int := S.Lb_int
      Lb_dual := S.Lb_dual
      Lb_index := S.Lb_index
      Uloc := fun v => (S.Uloc v).map (MulAut.conj (bc (prV (E := E) v) b)).toMonoidHom
      Uloc_le := by
        intro v
        rintro _ ⟨y, hy, rfl⟩
        have hbv : bc (prV (E := E) v) b ∈ UPts σ J (v.adicCompletion F) := (hlev v).1
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hbv (S.Uloc_le v hy)) (Subgroup.inv_mem _ hbv)
      Uloc_lev := by
        intro v
        rintro _ ⟨y, hy, rfl⟩
        have hbv := hlev v
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hbv (S.Uloc_lev v hy)) (Subgroup.inv_mem _ hbv)
      Uloc_hyp := by
        intro v hv hTv
        show (S.Uloc v).map (MulAut.conj (bc (prV (E := E) v) b)).toMonoidHom = levelVL σ J v S.Lb
        ext x
        rw [mem_map_conj, hone v hv hTv, inv_one, one_mul, mul_one, S.Uloc_hyp v hv hTv]
      fM := S.fM
      fM_acg := S.fM_acg
      fM_mod := S.fM_mod
      fT := S.fT
      fT_ne := S.fT_ne
      fT_T := S.fT_T
      fM_card := S.fM_card
      fT_L := S.fT_L
      UlocAlt := by
        intro v h
        show (S.Uloc v).map (MulAut.conj (bc (prV (E := E) v) b)).toMonoidHom = _
        rw [hT v h]
        exact S.UlocAlt v h
      U := S.U.map (MulAut.conj b).toMonoidHom
      U_eq := by
        intro x
        rw [mem_map_conj, S.U_eq, hP]
        refine and_congr_right fun _ => forall_congr' fun v => ?_
        rw [hbc v x]
        exact (mem_map_conj _ _ _).symm
      U_compact := by
        letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
        haveI := Formalism.L2.Col.rlt_topRing (F := F) (E := E)
        have hc : Continuous (fun x : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) => b * x * b⁻¹) :=
          (continuous_const.mul continuous_id).mul continuous_const
        have := S.U_compact.image hc
        convert this using 1
        rw [Subgroup.coe_map]
        rfl
      U_open := by
        letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
        haveI := Formalism.L2.Col.rlt_topRing (F := F) (E := E)
        haveI : ContinuousMul (UPts σ J (FiniteAdeleRing (𝓞 F) F)) :=
          inferInstanceAs (ContinuousMul (UPts σ J (FiniteAdeleRing (𝓞 F) F)).toSubmonoid)
        let b' : UPts σ J (FiniteAdeleRing (𝓞 F) F) := ⟨b, hb⟩
        have hc : Continuous (fun x : UPts σ J (FiniteAdeleRing (𝓞 F) F) => b'⁻¹ * x * b') :=
          (continuous_const.mul continuous_id).mul continuous_const
        have := S.U_open.preimage hc
        convert this using 1
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_preimage, mem_map_conj]
        rfl
      chi := S.chi.comp eqv.symm.toMonoidHom
      chi_triv := by
        intro x hx
        show S.chi (eqv.symm x) = 1
        apply S.chi_triv
        intro v hv
        have e1 : ((eqv.symm x : S.U) : GL (Fin n) _) = b⁻¹ * x.1 * b := by
          have h2 := heqv (eqv.symm x)
          rw [MulEquiv.apply_symm_apply] at h2
          rw [h2]
          group
        rw [e1, hbc v, hx v hv, mul_one, inv_mul_cancel] }
  refine ⟨S', rfl, rfl, fun x z hxz => ?_⟩
  show S.chi (eqv.symm x) = S.chi z
  congr 1
  rw [MulEquiv.symm_apply_eq]
  exact Subtype.ext (hxz.trans (heqv z).symm)

end GlobalTheory.Mem.Col2.ChEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStepPointGivenReductionsCosets
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.ChEx.TwLift

section Local

variable {E : Type} [Field E] [NumberField E]

theorem exists_pow_intAt_mul (P : HeightOneSpectrum (𝓞 E)) (c : E) :
    ∃ K : ℕ, ∀ e ∈ P.asIdeal ^ K, Formalism.L2.Col.IntAt P (algebraMap (𝓞 E) E e * c) := by
  by_cases hc : c = 0
  · refine ⟨0, fun e _ => ?_⟩
    rw [hc, mul_zero]
    simpa using Formalism.L2.Col.IntAt.coe P 0
  have h0 : P.valuation E c ≠ 0 := (Valuation.ne_zero_iff _).2 hc
  refine ⟨(WithZero.log (P.valuation E c)).toNat, fun e he => ?_⟩
  have h1 := (P.intValuation_le_pow_iff_mem e _).2 he
  have hv : P.valuation E (algebraMap (𝓞 E) E e * c) ≤ 1 := by
    rw [map_mul, HeightOneSpectrum.valuation_of_algebraMap]
    have hK := Int.self_le_toNat (WithZero.log (P.valuation E c))
    calc P.intValuation e * P.valuation E c
        ≤ WithZero.exp (-((WithZero.log (P.valuation E c)).toNat : ℤ)) * P.valuation E c := by gcongr
      _ = WithZero.exp (-((WithZero.log (P.valuation E c)).toNat : ℤ) + WithZero.log (P.valuation E c)) := by
          rw [WithZero.exp_add, WithZero.exp_log h0]
      _ ≤ 1 := by
          rw [← WithZero.exp_zero, WithZero.exp_le_exp]
          omega
  obtain ⟨r, s, hrs⟩ := P.exists_primeCompl_mul_eq_of_integer _ hv
  exact ⟨r, s, s.2, by rw [mul_comm]; exact hrs⟩

variable [StarRing E] {n : ℕ}

theorem exists_smul_of_mem_locP {P : HeightOneSpectrum (𝓞 E)} {N : Submodule (𝓞 E) (Sp E n)} {v : Sp E n}
    (hv : v ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N) : ∃ l : E, ∃ x ∈ N, v = l • x := by
  obtain ⟨s, hs, h⟩ := (mem_locP P N v).1 hv
  have hs0 : s ≠ 0 := fun e => hs (e ▸ P.asIdeal.zero_mem)
  have hs1 : algebraMap (𝓞 E) E s ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).2 hs0
  refine ⟨(algebraMap (𝓞 E) E s)⁻¹, s • v, h, ?_⟩
  rw [← algebraMap_smul E s v, inv_smul_smul₀ hs1]

theorem exists_approx (T : Finset (HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Sp E n)) (c : T → E) (a : T → Sp E n)
    (ha : ∀ P, ∃ l : E, ∃ x ∈ N, a P = l • x) :
    ∃ y : Sp E n, ∀ P : T, c P • (y - a P) ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal N := by
  classical
  choose l x hx hax using ha
  choose K hK using fun P P' : T => exists_pow_intAt_mul P'.1 (c P' * l P)
  have he : ∀ P : T, ∃ e : 𝓞 E, ∀ P' : T, e - (if P = P' then 1 else 0) ∈ P'.1.asIdeal ^ (∑ P'' : T, K P'' P') := by
    intro P
    obtain ⟨e, he⟩ := exists_forall_sub_mem_ideal (s := (Finset.univ : Finset T)) (fun Q : T => Q.1.asIdeal)
      (fun Q : T => ∑ P'' : T, K P'' Q) (fun Q _ => Q.1.prime)
      (fun Q _ Q' _ hne h => hne (Subtype.ext (HeightOneSpectrum.ext h))) (fun Q => if P = Q.1 then 1 else 0)
    exact ⟨e, fun P' => he P' (Finset.mem_univ _)⟩
  choose e he using he
  refine ⟨∑ P, (algebraMap (𝓞 E) E (e P) * l P) • x P, fun P0 => ?_⟩
  have hsum : (∑ P, (algebraMap (𝓞 E) E (e P) * l P) • x P) - a P0 =
      ∑ P, (algebraMap (𝓞 E) E (e P - if P = P0 then 1 else 0) * l P) • x P := by
    symm
    have h1 : ∀ P, (algebraMap (𝓞 E) E (e P - if P = P0 then 1 else 0) * l P) • x P =
        (algebraMap (𝓞 E) E (e P) * l P) • x P - (if P = P0 then l P0 • x P0 else 0) := by
      intro P
      split_ifs with hP
      · subst hP
        rw [map_sub, map_one, _root_.sub_mul, one_mul, sub_smul]
      · rw [sub_zero, sub_zero]
    rw [Finset.sum_congr rfl (fun P _ => h1 P), Finset.sum_sub_distrib, hax P0]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hsum, Finset.smul_sum]
  refine Submodule.sum_mem _ fun P _ => ?_
  rw [smul_smul]
  have e1 : c P0 * (algebraMap (𝓞 E) E (e P - if P = P0 then 1 else 0) * l P) =
      algebraMap (𝓞 E) E (e P - if P = P0 then 1 else 0) * (c P0 * l P) := by ring
  rw [e1]
  exact GlobalTheory.TopStep.smul_mem_locP (hK P P0 _ (Ideal.pow_le_pow_right
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ P)) (he P P0)))
    (Formalism.L2.Col.le_locP _ _ (hx P))

end Local

end GlobalTheory.Mem.Col2.ChEx.TwLift

namespace GlobalTheory.Mem.Col2.ChEx.TwLift

section Pt

variable {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {u : Pr.Word} {j : ℕ}

open Classical in

theorem frsF_mem (p : ChPt (R := R) sel mu u j) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs) (x : Sp X.E (R.N j)) :
    frsF sel mu p P x ∈ p.deco.1.at P.1 ↔ x ∈ stdAt X.E (R.N j) P.1 := by
  unfold frsF
  rw [dif_neg hP]
  exact p.2 ⟨P.1, (Finset.mem_union.mp P.2).resolve_left hP⟩ x

theorem frsF_symm_mem (p : ChPt (R := R) sel mu u j) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs) (v : Sp X.E (R.N j)) :
    (frsF sel mu p P).symm v ∈ stdAt X.E (R.N j) P.1 ↔ v ∈ p.deco.1.at P.1 := by
  rw [← frsF_mem p P hP, LinearEquiv.apply_symm_apply]

open Classical in

theorem cosetIn_eq {cst : LocCst X (rowSG Pr sel mu)} (q : PtAt R sel mu cst u j) {y : Sp X.E (R.N j)}
    (hY : q.1.2 = {z | z - y ∈ locLat (rowSG Pr sel mu) q.1.1.deco.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ))})
    (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs) :
    cosetIn q P = {z | ((qOf P.1 : X.E) ^ cst.M)⁻¹ • (z - (frsF sel mu q.1.1 P).symm y) ∈ stdAt X.E (R.N j) P.1} := by
  ext z
  simp only [cosetIn, if_neg hP, hY, Set.mem_setOf_eq]
  constructor
  · rintro ⟨y0, hy0, hz⟩
    have h1 := (mem_locLat _ _ _ _).1 hy0 P
    rw [if_neg hP, zpow_natCast] at h1
    have h2 := (frsF_symm_mem q.1.1 P hP _).2 h1
    rw [map_smul, map_sub] at h2
    have e : ((qOf P.1 : X.E) ^ cst.M)⁻¹ • (z - (frsF sel mu q.1.1 P).symm y) =
        ((qOf P.1 : X.E) ^ cst.M)⁻¹ • (z - (frsF sel mu q.1.1 P).symm y0) +
          ((qOf P.1 : X.E) ^ cst.M)⁻¹ • ((frsF sel mu q.1.1 P).symm y0 - (frsF sel mu q.1.1 P).symm y) := by
      rw [← smul_add]
      congr 1
      abel
    rw [e]
    exact add_mem hz h2
  · intro hz
    exact ⟨y, by rw [sub_self]; exact zero_mem _, hz⟩

end Pt

theorem exists_ptAt_bar_cq_eq : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, (∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) → ∀ (r : PtAt R sel mu cst u j) (p : ChPt (R := R) sel mu u j), ∃ r' : PtAt R sel mu cst u j, r'.1.1 = p ∧ bar r' = bar r ∧ GlobalTheory.Mem.Col2.ChEx.cqOf r' = GlobalTheory.Mem.Col2.ChEx.cqOf r := by
  intro X Pr R sel S mu cst u j hQ r p
  classical
  by_cases h : j + 1 = R.m
  · obtain ⟨y, hy, hY⟩ := r.mem_ybSet h
    have hyG : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → ((qOf P.1 : ℕ) : X.E) • y ∈ r.1.1.deco.1.at P.1 := fun P hP => by
      have h1 := (mem_locLat _ _ _ _).1 hy P
      rwa [if_pos hP, _root_.zpow_neg_one, inv_inv] at h1
    have hyQ : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → ((qOf P.1 : X.E) ^ cst.M) • y ∈ r.1.1.deco.1.at P.1 := fun P hP => by
      have h1 := (mem_locLat _ _ _ _).1 hy P
      rwa [if_neg hP, _root_.zpow_neg, inv_inv, zpow_natCast] at h1
    choose xw hxN hxv using fun w : Pr.vGs => p.deco.2.be_surj w (r.1.1.deco.1.be w (((qOf w.1 : ℕ) : X.E) • y))
    let a : rowSG Pr sel mu → Sp X.E (R.N j) := fun P =>
      if hP : P.1 ∈ Pr.vGs then (((qOf P.1 : ℕ) : X.E))⁻¹ • xw ⟨P.1, hP⟩ else frsF sel mu p P ((frsF sel mu r.1.1 P).symm y)
    let c : rowSG Pr sel mu → X.E := fun P => ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹
    have haG : ∀ (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs), a P = (((qOf P.1 : ℕ) : X.E))⁻¹ • xw ⟨P.1, hP⟩ := fun P hP => dif_pos hP
    have haQ : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → a P = frsF sel mu p P ((frsF sel mu r.1.1 P).symm y) := fun P hP => dif_neg hP
    have hQa : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → ((qOf P.1 : X.E) ^ cst.M) • a P ∈ p.deco.1.at P.1 := fun P hP => by
      rw [haQ P hP, ← map_smul, frsF_mem p P hP, ← map_smul, frsF_symm_mem r.1.1 P hP]
      exact hyQ P hP
    have ha : ∀ P, ∃ l : X.E, ∃ x ∈ p.deco.1.N, a P = l • x := fun P => by
      by_cases hP : P.1 ∈ Pr.vGs
      · exact ⟨_, _, hxN _, haG P hP⟩
      · obtain ⟨l, x, hx, e⟩ := exists_smul_of_mem_locP (hQa P hP)
        refine ⟨((qOf P.1 : X.E) ^ cst.M)⁻¹ * l, x, hx, ?_⟩
        rw [mul_smul, ← e, inv_smul_smul₀ (pow_ne_zero _ GlobalTheory.TopStep.qOf_ne_zero)]
    obtain ⟨y', hy'⟩ := exists_approx (rowSG Pr sel mu) p.deco.1.N c a ha
    have hy'G : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → y' - a P ∈ p.deco.1.at P.1 := fun P hP => by
      have h1 := hy' P
      simp only [c, if_pos hP, pow_zero, inv_one, one_smul] at h1
      exact h1
    have hy'Q : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → ((qOf P.1 : X.E) ^ cst.M)⁻¹ • (y' - a P) ∈ p.deco.1.at P.1 := fun P hP => by
      have h1 := hy' P
      simp only [c, if_neg hP] at h1
      exact h1
    have eG : ∀ (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs), ((qOf P.1 : ℕ) : X.E) • y' =
        xw ⟨P.1, hP⟩ + ((qOf P.1 : ℕ) : X.E) • (y' - a P) := fun P hP => by
      rw [haG P hP, smul_sub, smul_inv_smul₀ GlobalTheory.TopStep.qOf_ne_zero, add_sub_cancel]
    have hG : ∀ w : Pr.vGs, w.1 ∈ rowSG Pr sel mu := fun w => Finset.mem_union_left _ w.2
    refine ⟨⟨(p, {z | z - y' ∈ locLat (rowSG Pr sel mu) p.deco.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ))}), ?_⟩,
      rfl, ?_, ?_⟩
    · rw [ysAt_ys_of_eq sel mu cst h]
      refine ⟨y', (mem_locLat _ _ _ _).2 fun P => ?_, rfl⟩
      by_cases hP : P.1 ∈ Pr.vGs
      · rw [if_pos hP, _root_.zpow_neg_one, inv_inv]
        show _ ∈ p.deco.1.at P.1
        rw [eG P hP]
        exact add_mem (Formalism.L2.Col.le_locP _ _ (hxN _)) (GlobalTheory.TopStep.smul_mem_locP (GlobalTheory.TopStep.intAt_nat _) (hy'G P hP))
      · rw [if_neg hP, _root_.zpow_neg, inv_inv, zpow_natCast]
        show _ ∈ p.deco.1.at P.1
        have e : ((qOf P.1 : X.E) ^ cst.M) • y' = ((qOf P.1 : X.E) ^ cst.M) • a P +
            ((qOf P.1 : X.E) ^ cst.M * (qOf P.1 : X.E) ^ cst.M) • (((qOf P.1 : X.E) ^ cst.M)⁻¹ • (y' - a P)) := by
          rw [smul_smul, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ GlobalTheory.TopStep.qOf_ne_zero), mul_one, smul_sub, add_sub_cancel]
        rw [e]
        exact add_mem (hQa P hP) (GlobalTheory.TopStep.smul_mem_locP
          ((GlobalTheory.TopStep.intAt_pow (GlobalTheory.TopStep.intAt_nat _) _).mul (GlobalTheory.TopStep.intAt_pow (GlobalTheory.TopStep.intAt_nat _) _)) (hy'Q P hP))
    · funext w
      have hw := hG w
      have hmem : ((qOf w.1 : ℕ) : X.E) • y' ∈ p.deco.1.at w.1 := by
        rw [eG ⟨w.1, hw⟩ w.2]
        exact add_mem (Formalism.L2.Col.le_locP _ _ (hxN _))
          (GlobalTheory.TopStep.smul_mem_locP (GlobalTheory.TopStep.intAt_nat _) (hy'G ⟨w.1, hw⟩ w.2))
      have key : p.deco.1.be w (((qOf w.1 : ℕ) : X.E) • y') = r.1.1.deco.1.be w (((qOf w.1 : ℕ) : X.E) • y) := by
        rw [eG ⟨w.1, hw⟩ w.2, p.deco.2.be_add w _ (Formalism.L2.Col.le_locP _ _ (hxN _)) _
          (GlobalTheory.TopStep.smul_mem_locP (GlobalTheory.TopStep.intAt_nat _) (hy'G ⟨w.1, hw⟩ w.2)),
          GlobalTheory.TopStep.be_smul_int p.deco.2 w (GlobalTheory.TopStep.intAt_nat _) (hy'G ⟨w.1, hw⟩ w.2), GlobalTheory.TopStep.reduction_absNorm_eq_zero, zero_smul,
          add_zero]
        exact hxv w
      refine (MemChart.CosetLift.coset_be p.deco _ w hw _ (if_pos w.2) hmem).trans ?_
      rw [key, MemChart.bar, hY]
      exact (MemChart.CosetLift.coset_be r.1.1.deco _ w hw _ (if_pos w.2) (hyG ⟨w.1, hw⟩ w.2)).symm
    · funext P
      have hP : (⟨P.1, Finset.mem_union_right _ P.2⟩ : rowSG Pr sel mu).1 ∉ Pr.vGs := hQ P.1 P.2
      unfold GlobalTheory.Mem.Col2.ChEx.cqOf
      rw [cosetIn_eq r hY _ hP]
      refine (cosetIn_eq _ (y := y') ?_ _ hP).trans ?_
      · rfl
      set P' : rowSG Pr sel mu := ⟨P.1, Finset.mem_union_right _ P.2⟩
      set cM : X.E := ((qOf P'.1 : X.E) ^ cst.M)⁻¹
      have key : cM • ((frsF sel mu p P').symm y' - (frsF sel mu r.1.1 P').symm y) ∈ stdAt X.E (R.N j) P'.1 := by
        have e1 : (frsF sel mu r.1.1 P').symm y = (frsF sel mu p P').symm (a P') := by
          rw [haQ P' hP, LinearEquiv.symm_apply_apply]
        rw [e1, ← map_sub, ← map_smul, frsF_symm_mem p P' hP]
        exact hy'Q P' hP
      ext z
      simp only [Set.mem_setOf_eq]
      have e : cM • (z - (frsF sel mu r.1.1 P').symm y) =
          cM • (z - (frsF sel mu p P').symm y') + cM • ((frsF sel mu p P').symm y' - (frsF sel mu r.1.1 P').symm y) := by
        rw [← smul_add]
        congr 1
        abel
      constructor
      · intro hz
        change cM • (z - (frsF sel mu r.1.1 P').symm y) ∈ stdAt X.E (R.N j) P'.1
        rw [e]
        exact add_mem hz key
      · intro hz
        change cM • (z - (frsF sel mu p P').symm y') ∈ stdAt X.E (R.N j) P'.1
        have e2 : cM • (z - (frsF sel mu p P').symm y') = cM • (z - (frsF sel mu r.1.1 P').symm y) -
            cM • ((frsF sel mu p P').symm y' - (frsF sel mu r.1.1 P').symm y) := by
          rw [e, add_sub_cancel_right]
        rw [e2]
        exact sub_mem hz key
  · have hY : r.1.2 = ∅ := by
      have := r.2
      rwa [ysAt_ys_of_ne sel mu cst h] at this
    refine ⟨⟨(p, ∅), by rw [ysAt_ys_of_ne sel mu cst h]; rfl⟩, rfl, ?_, ?_⟩
    · funext w
      simp [MemChart.bar, hY]
    · funext P
      simp [GlobalTheory.Mem.Col2.ChEx.cqOf, cosetIn, hY]

end GlobalTheory.Mem.Col2.ChEx.TwLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTopStepLevelCongruentBlockSumOne
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT

open GlobalTheory.TopStep

section Local

variable {E : Type} [Field E] {N : ℕ}

theorem prXpG_sumE (hN : N = (N - 1) + 1) (g : Sp E (N - 1) ≃ₗ[E] Sp E (N - 1)) :
    prXpG E N ∘ₗ (sumE hN g 1).toLinearMap = (g.toLinearMap : Sp E ((N - 1) + 0) →ₗ[E] Sp E ((N - 1) + 0)) ∘ₗ prXpG E N := by
  refine LinearMap.ext fun x => funext fun i => ?_

  exact congrFun (prH_sumE hN g 1 x) i

theorem atNL_sumE (hN : N = (N - 1) + 1) (g : Sp E (N - 1) ≃ₗ[E] Sp E (N - 1)) :
    atNL E N (N - 1) ∘ₗ (sumE hN g 1).toLinearMap = atNL E N (N - 1) := by
  refine LinearMap.ext fun x => ?_
  have hlt : N - 1 < N := by omega

  have h := sumE_last hN g 1 x
  rw [Units.val_one, one_mul] at h
  simp only [LinearMap.comp_apply, atNL, dif_pos hlt, LinearMap.proj_apply]
  exact h

end Local

end GlobalTheory.Mem.Col2.AdT

namespace GlobalTheory.Mem.Col2.AdT

open GlobalTheory.TopStep

theorem exists_topLev_liftsInv : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ), i = B.R.m →
    ∀ (b : (I.stp u a i).β) (κ : (I.stp u a i).G b) (P : SBof I a), ∃ g g' z,
      GlobalTheory.TwU.TopLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) i P g z ∧ LiftsInv I κ P g' ∧
        CongE P.1 (GlobalTheory.TwU.topDep I.sel (I.tup a) (I.cst a) P) g g' := by
  intro B X I hI u a i hi b κ P
  subst hi

  rcases b with ⟨_ | b₀, hb⟩
  swap
  · exact absurd (hb.mp rfl) (lt_irrefl _)
  have hPr := (GlobalTheory.BasePrimes.primes_ok B X).1

  have hq : ((qOf P.1 : ℕ) : 𝓞 B.fields.E) ∉ P.1.asIdeal ^ 2 :=
    Formalism.L2.Ker.mq_rowSG_unif (I.tup a) (GlobalTheory.Mem.FieldsLaws.fields_ok (B := B)) hPr hI.sel_ok P
  have hN := N_m_succ B.R
  by_cases hP : P.1 ∈ (B.primes X).vGs
  ·
    have hQn : P.1 ∉ I.Q a := QE_disj (I.tup a) hPr hI.sel_ok hI.g_mem P.1 hP
    have hmem : κ.2.1.1 ⟨P.1, hP⟩ ∈ (levGTop I.Ch I.Ps ⟨P.1, hP⟩).H := by
      have h := κ.2.1.2
      simp only [LevFam.grp, Subgroup.mem_pi] at h
      rw [← topLev_levG_m I.Ch I.sel (I.tup a) (I.cst a) I.Ps]
      exact h ⟨P.1, hP⟩ (Set.mem_univ _)
    obtain ⟨h₀, hh₀, hdiag⟩ := (mem_levDiag _ _ _).mp hmem
    rw [rowTyG_PsymF_H] at hh₀
    have hr : B.R.r = B.R.k + 2 * B.R.rS + 1 := by
      simp only [Formalism.BasicNotions.Ranks.rS, Formalism.BasicNotions.Ranks.r]
      obtain ⟨s, hs⟩ := B.R.m_even
      have := B.R.two_le_m
      omega
    have hsym : rSym B.R.k B.R.rS = B.R.r := by rw [hr]; rfl

    have hJ := (mem_HJsym_iff_JSymG (𝓞 B.fields.E ⧸ P.1.asIdeal) (B.R.N B.R.m - 1) B.R.k B.R.r B.R.t B.R.m B.R.rS
      (r_le_X' B.R) hr B.R.t_odd.pos (rank_X'_eq B.R) h₀⁻¹).mp (Subgroup.inv_mem _ hh₀)

    obtain ⟨j, hj⟩ := redGL_surjective (E := B.fields.E) (n := B.R.N B.R.m - 1) P.1 h₀⁻¹
    have hjinv : redGL _ P.1 j⁻¹ = h₀ := by rw [map_inv, hj, inv_inv]
    have hlev : j.1 ∈ GlobalTheory.TwU.rowLevTop (B.primes X) B.R (I.cst a).sharp (B.R.N B.R.m) P.1 := by
      have h := GlobalTheory.Mem.LastGrp.mem_JGsym0 (fun x hx h0 => intAt_div_of_redP hq hx h0)
        (hsym.symm ▸ r_le_X' B.R) j
        (fun x y hxy => by rw [← redGL_val, hj]; exact hJ.1.1 x y hxy)
        (fun x y hxy => by rw [← redGL_val, hjinv]; simpa using hJ.2.1 x y hxy)
        (fun x hx => by rw [← redGL_val, hj]; exact hJ.1.2.1 x hx)
        (fun x y hx hy => by rw [← redGL_val, hj]; exact hJ.1.2.2.1 x y hx hy)
      have e : GlobalTheory.CongLevel.extE 0 j.1 = j.1 := LinearEquiv.ext (GlobalTheory.Mem.LastGrp.extE_zero j.1)
      rw [e, hsym] at h
      simp only [GlobalTheory.TwU.rowLevTop, if_pos hP, hI.sharp a, if_true]
      exact h
    refine ⟨sumE hN j.1 1, sumE hN j.1 1, _, ⟨j.1, hlev, prXpG_sumE hN j.1, atNL_sumE hN j.1, rfl⟩, ⟨?_, ?_, ?_⟩, congE_refl _ _ _⟩
    · rw [← extI_val hN j]
      exact (extI hN P.1 j).2
    · intro h x hx
      rw [← extI_val hN j, redV_redGL _ hx, redGL_extI, hj, ← hdiag, ← map_inv]
    · exact fun h => absurd h hQn
  ·
    have hQ : P.1 ∈ I.Q a := by
      classical
      have h := P.2
      simp only [SBof, rowSG, uSG, Finset.mem_union] at h
      exact h.resolve_left hP
    have hmem : κ.2.2.1 ⟨P.1, hQ⟩ ∈ (levQTop B.R I.sel (I.tup a) (topDep B.R (I.cst a).M) ⟨P.1, hQ⟩).H := by
      have h := κ.2.2.2
      simp only [LevQFam.grp, Subgroup.mem_pi] at h
      rw [← topLev_levQ_m I.Ch I.sel (I.tup a) (I.cst a) I.Ps]
      exact h ⟨P.1, hQ⟩ (Set.mem_univ _)
    simp only [levQTop] at hmem
    obtain ⟨j, hj, hjc⟩ := (mem_levCong _ _ _ _).mp (Subgroup.inv_mem _ hmem)
    have hlev : j.1 ∈ GlobalTheory.TwU.rowLevTop (B.primes X) B.R (I.cst a).sharp (B.R.N B.R.m) P.1 := by
      simp only [GlobalTheory.TwU.rowLevTop, if_neg hP]
      exact GlobalTheory.TopLaw.mem_JQ_of_red hq j ((mem_levRed _ _).mp hj)
    refine ⟨sumE hN j.1 1, ((κ.2.2.1 ⟨P.1, hQ⟩)⁻¹).1, _, ⟨j.1, hlev, prXpG_sumE hN j.1, atNL_sumE hN j.1, rfl⟩,
      ⟨((κ.2.2.1 ⟨P.1, hQ⟩)⁻¹).2, fun h => absurd h hP, fun h => rfl⟩, ?_⟩

    have h2 : (extI hN P.1 j)⁻¹ * (κ.2.2.1 ⟨P.1, hQ⟩)⁻¹ ∈ prinCong _ P.1 (2 * (I.cst a).M) :=
      prinCong_anti (by have := two_mul_le_topDep B.R (I.cst a).M; omega) hjc
    have h3 : ((κ.2.2.1 ⟨P.1, hQ⟩)⁻¹)⁻¹ * extI hN P.1 j ∈ prinCong _ P.1 (2 * (I.cst a).M) := by
      have := Subgroup.inv_mem _ h2
      rwa [_root_.mul_inv_rev, inv_inv] at this
    have h4 := (inv_mul_mem_prinCong _ _ _).mp h3
    intro x hx
    simp only [GlobalTheory.TwU.topDep, if_neg hP]
    have := h4 x hx
    rwa [extI_val] at this

end GlobalTheory.Mem.Col2.AdT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemFramedLevelIffTwoAdelicPointsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_framedLevel_iff_two_adelic_points : ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (Λ : LevFam E K n SG) (Θ : LevQFam E K n Q) (d : Q → E) (hd : ∀ P, d P ≠ 0) (N : Q → ℕ) (hdN : ∀ P : Q, P.1.valuation E (d P) ≤ WithZero.exp (-(N P : ℤ))) (hΘ : ∀ (P : Q) (g : ↥(GLint E n P.1)), lqPrinc P.1 (N P) (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1) (U : Subgroup (GL (Fin n) (AfE F E))) (k t y x : GL (Fin n) (AfE F E)) (p p' : DecoF E n ST SG Q), k ∈ UAd hc n → (∀ P : Q, rhoP F P.1 k = 1) → t ∈ K1 hc n ST SG → (∀ x ∈ UAd hc n, x ∈ U ↔ k⁻¹ * x * k ∈ levU hc n ST SG Λ.grp) → IsPtOf hc (y * (k * t)) p → IsPtOf hc (y * x * (k * t)) p' → (x ∈ topU U t Θ d ↔ ∃ (h : Λ.grp) (θ : Θ.grp), ((1, h.1, θ.1) : UF E n × GLG E n SG × GLQ E n Q) • p = p') := by
  first | exact @GlobalTheory.Mem.Col2.TopCh.mem_topU_iff | exact GlobalTheory.Mem.Col2.TopCh.mem_topU_iff | (intros; apply GlobalTheory.Mem.Col2.TopCh.mem_topU_iff <;> assumption)
end

