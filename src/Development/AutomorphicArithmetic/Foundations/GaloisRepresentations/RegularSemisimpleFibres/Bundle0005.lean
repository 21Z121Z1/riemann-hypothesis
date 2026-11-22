import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Bundle0002
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0030

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PParCons
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section ParConsAux

variable {F : Type} [Field F]

private theorem tl_entry {a n : ℕ} (M : Matrix (Fin n) (Fin n) F) (i j : Fin a) (I J : Fin n)
    (hI : (I : ℕ) = i) (hJ : (J : ℕ) = j) : GlobalTheory.Shin.tl a M i j = M I J := by
  unfold GlobalTheory.Shin.tl GlobalTheory.Shin.ent
  rw [dif_pos ⟨by rw [← hI]; exact I.isLt, by rw [← hJ]; exact J.isLt⟩]
  congr 1 <;> ext <;> simp [hI, hJ]

private theorem br_entry {a b n : ℕ} (M : Matrix (Fin n) (Fin n) F) (i j : Fin b) (I J : Fin n)
    (hI : (I : ℕ) = a + i) (hJ : (J : ℕ) = a + j) : GlobalTheory.Shin.br a b M i j = M I J := by
  unfold GlobalTheory.Shin.br GlobalTheory.Shin.ent
  rw [dif_pos ⟨by rw [← hI]; exact I.isLt, by rw [← hJ]; exact J.isLt⟩]
  congr 1 <;> ext <;> simp [hI, hJ]

private theorem units_of {a b n : ℕ} (hn : n = a + b) (p : GL (Fin n) F) (h : GlobalTheory.Shin.InPar a p) :
    IsUnit (GlobalTheory.Shin.tl a (p : Matrix (Fin n) (Fin n) F)) ∧
      IsUnit (GlobalTheory.Shin.br a b (p : Matrix (Fin n) (Fin n) F)) := by
  subst hn
  have hM : (p : Matrix (Fin (a + b)) (Fin (a + b)) F).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks (GlobalTheory.Shin.tl a (p : Matrix (Fin (a + b)) (Fin (a + b)) F))
        (Matrix.of fun i j => (p : Matrix (Fin (a + b)) (Fin (a + b)) F) (Fin.castAdd b i) (Fin.natAdd a j)) 0
        (GlobalTheory.Shin.br a b (p : Matrix (Fin (a + b)) (Fin (a + b)) F)) := by
    refine Matrix.ext fun i j => ?_
    rcases i with i | i <;> rcases j with j | j
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁, finSumFinEquiv_apply_left]
      exact (tl_entry _ i j _ _ (by simp) (by simp)).symm
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂, finSumFinEquiv_apply_left,
        finSumFinEquiv_apply_right, Matrix.of_apply]
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁, finSumFinEquiv_apply_left,
        finSumFinEquiv_apply_right, Matrix.zero_apply]
      exact h _ _ (by simp) (by simp)
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂, finSumFinEquiv_apply_right]
      exact (br_entry _ i j _ _ (by simp) (by simp)).symm
  have hu : IsUnit (p : Matrix (Fin (a + b)) (Fin (a + b)) F).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 p.isUnit
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv, hM, Matrix.det_fromBlocks_zero₂₁,
    IsUnit.mul_iff] at hu
  exact ⟨(Matrix.isUnit_iff_isUnit_det _).2 hu.1, (Matrix.isUnit_iff_isUnit_det _).2 hu.2⟩

private theorem toG_coe {n : ℕ} {M : Matrix (Fin n) (Fin n) F} (h : IsUnit M) :
    ((GlobalTheory.Shin.toG M : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = M := by
  unfold GlobalTheory.Shin.toG
  rw [dif_pos h]
  rfl

private theorem sv0 {s n : ℕ} (d : Fin (s + 1) → ℕ) (hd : ∑ i, d i = n) (i : Fin (d 0)) :
    ((GlobalTheory.SmGL.stdBlocks d hd ⟨0, i⟩ : Fin n) : ℕ) = i := by
  rw [GlobalTheory.SmGL.stdBlocks_val]
  simp

private theorem svS {s n b : ℕ} (d : Fin (s + 1) → ℕ) (hd : ∑ i, d i = n)
    (hb : ∑ i : Fin s, d i.succ = b) (c : Fin s) (i : Fin (d c.succ)) :
    ((GlobalTheory.SmGL.stdBlocks d hd ⟨c.succ, i⟩ : Fin n) : ℕ) =
      d 0 + ((GlobalTheory.SmGL.stdBlocks (fun i : Fin s => d i.succ) hb ⟨c, i⟩ : Fin b) : ℕ) := by
  rw [GlobalTheory.SmGL.stdBlocks_val, GlobalTheory.SmGL.stdBlocks_val]
  erw [Fin.sum_univ_succ]
  rw [add_assoc]
  congr 2

private theorem inPar_of {s n b : ℕ} (d : Fin (s + 1) → ℕ) (hd : ∑ i, d i = n)
    (hb : ∑ i : Fin s, d i.succ = b) (p : GL (Fin n) F)
    (hp : p ∈ GlobalTheory.SmGL.parab F (GlobalTheory.SmGL.stdBlocks d hd)) : GlobalTheory.Shin.InPar (d 0) p := by
  intro i j hj hi
  obtain ⟨⟨α, i'⟩, rfl⟩ := (GlobalTheory.SmGL.stdBlocks d hd).surjective i
  obtain ⟨⟨β, j'⟩, rfl⟩ := (GlobalTheory.SmGL.stdBlocks d hd).surjective j
  rw [GlobalTheory.SmGL.mem_parab_iff] at hp
  cases β using Fin.cases with
  | zero =>
    cases α using Fin.cases with
    | zero =>
      rw [sv0] at hi
      exact absurd i'.isLt (by omega)
    | succ c => exact hp _ _ _ _ (Fin.succ_pos c)
  | succ c =>
    rw [svS d hd hb] at hj
    omega

private theorem brG_entry {s n b : ℕ} (d : Fin (s + 1) → ℕ) (hd : ∑ i, d i = n)
    (hb : ∑ i : Fin s, d i.succ = b) (hn : n = d 0 + b) (p : GL (Fin n) F)
    (h : GlobalTheory.Shin.InPar (d 0) p) (c c' : Fin s) (i : Fin (d c.succ)) (j : Fin (d c'.succ)) :
    ((GlobalTheory.Shin.brG (d 0) b p : GL (Fin b) F) : Matrix (Fin b) (Fin b) F)
        (GlobalTheory.SmGL.stdBlocks (fun i : Fin s => d i.succ) hb ⟨c, i⟩)
        (GlobalTheory.SmGL.stdBlocks (fun i : Fin s => d i.succ) hb ⟨c', j⟩) =
      (p : Matrix (Fin n) (Fin n) F) (GlobalTheory.SmGL.stdBlocks d hd ⟨c.succ, i⟩)
        (GlobalTheory.SmGL.stdBlocks d hd ⟨c'.succ, j⟩) := by
  unfold GlobalTheory.Shin.brG
  rw [toG_coe (units_of hn p h).2]
  exact br_entry _ _ _ _ _ (svS d hd hb c i) (svS d hd hb c' j)

end ParConsAux

theorem UpperTheory.Gal.InertialTypesAlt.parCons :
    ParCons := by
  intro F _ s n d hd b hb p
  have hn : n = d 0 + b := by rw [← hd, ← hb, Fin.sum_univ_succ]
  refine ⟨⟨fun hp => ⟨inPar_of d hd hb p hp, ?_⟩, fun ⟨h1, h2⟩ => ?_⟩, fun hp hp' => ⟨?_, fun c => ?_⟩⟩
  · have h1 := inPar_of d hd hb p hp
    rw [GlobalTheory.SmGL.mem_parab_iff] at hp ⊢
    intro c c' i j hc
    rw [brG_entry d hd hb hn p h1]
    exact hp _ _ _ _ (Fin.succ_lt_succ_iff.2 hc)
  · rw [GlobalTheory.SmGL.mem_parab_iff] at h2 ⊢
    intro α β i j hαβ
    cases α using Fin.cases with
    | zero => exact absurd hαβ (Fin.not_lt_zero _)
    | succ c =>
      cases β using Fin.cases with
      | zero =>
        apply h1
        · rw [sv0]; exact j.isLt
        · rw [svS d hd hb]; omega
      | succ c' =>
        rw [← brG_entry d hd hb hn p h1]
        exact h2 _ _ _ _ (Fin.succ_lt_succ_iff.1 hαβ)
  · have h1 := inPar_of d hd hb p hp
    ext i j
    change (p : Matrix (Fin n) (Fin n) F) (GlobalTheory.SmGL.stdBlocks d hd ⟨0, i⟩)
      (GlobalTheory.SmGL.stdBlocks d hd ⟨0, j⟩) = _
    unfold GlobalTheory.Shin.tlG
    rw [toG_coe (units_of hn p h1).1]
    exact (tl_entry _ _ _ _ _ (sv0 d hd i) (sv0 d hd j)).symm
  · have h1 := inPar_of d hd hb p hp
    ext i j
    change (p : Matrix (Fin n) (Fin n) F) (GlobalTheory.SmGL.stdBlocks d hd ⟨c.succ, i⟩)
        (GlobalTheory.SmGL.stdBlocks d hd ⟨c.succ, j⟩) =
      ((GlobalTheory.Shin.brG (d 0) b p : GL (Fin b) F) : Matrix (Fin b) (Fin b) F)
        (GlobalTheory.SmGL.stdBlocks (fun i : Fin s => d i.succ) hb ⟨c, i⟩)
        (GlobalTheory.SmGL.stdBlocks (fun i : Fin s => d i.succ) hb ⟨c, j⟩)
    rw [brG_entry d hd hb hn p h1]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PResCl
section
noncomputable section

open GlobalTheory.Shin

namespace UpperTheory.Gal.InertialTypesAlt

section Blocks

variable {F : Type} [Field F] {a b : ℕ}

private def blk (M : Matrix (Fin (a + b)) (Fin (a + b)) F) :
    Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) F :=
  M.submatrix finSumFinEquiv finSumFinEquiv

private theorem blk_mul (M N : Matrix (Fin (a + b)) (Fin (a + b)) F) :
    blk (M * N) = blk M * blk N :=
  (Matrix.submatrix_mul_equiv M N _ _ _).symm

private theorem tl_eq (M : Matrix (Fin (a + b)) (Fin (a + b)) F) :
    tl a M = (blk M).toBlocks₁₁ := by
  ext i j
  have hi : (i : ℕ) < a + b := by omega
  have hj : (j : ℕ) < a + b := by omega
  simp [tl, ent, blk, Matrix.toBlocks₁₁, hi, hj]
  rfl

private theorem br_eq (M : Matrix (Fin (a + b)) (Fin (a + b)) F) :
    br a b M = (blk M).toBlocks₂₂ := by
  ext i j
  simp [br, ent, blk, Matrix.toBlocks₂₂]
  rfl

private theorem inPar_iff (x : GL (Fin (a + b)) F) :
    InPar a x ↔ (blk (x : Matrix (Fin (a + b)) (Fin (a + b)) F)).toBlocks₂₁ = 0 := by
  constructor
  · intro h
    ext i j
    exact h _ _ (by simp) (by simp)
  · intro h i j hj hi
    obtain ⟨i', rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j', rfl⟩ := finSumFinEquiv.surjective j
    rcases j' with j' | j'
    · rcases i' with i' | i'
      · simp at hi; omega
      · exact congrFun (congrFun h i') j'
    · simp at hj

private def dg (a : ℕ) (z : GL (Fin b) F) : GL (Fin (a + b)) F where
  val := (Matrix.fromBlocks 1 0 0 (z : Matrix (Fin b) (Fin b) F)).submatrix
    finSumFinEquiv.symm finSumFinEquiv.symm
  inv := (Matrix.fromBlocks 1 0 0 ((z⁻¹ : GL (Fin b) F) : Matrix (Fin b) (Fin b) F)).submatrix
    finSumFinEquiv.symm finSumFinEquiv.symm
  val_inv := by
    rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp
  inv_val := by
    rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp

private theorem blk_conj (z : GL (Fin b) F) (p : GL (Fin (a + b)) F) :
    blk (((dg a z)⁻¹ * p * dg a z : GL (Fin (a + b)) F) : Matrix (Fin (a + b)) (Fin (a + b)) F) =
      Matrix.fromBlocks (blk (p : Matrix (Fin (a + b)) (Fin (a + b)) F)).toBlocks₁₁
        ((blk (p : Matrix (Fin (a + b)) (Fin (a + b)) F)).toBlocks₁₂ * (z : Matrix (Fin b) (Fin b) F))
        (((z⁻¹ : GL (Fin b) F) : Matrix (Fin b) (Fin b) F) *
          (blk (p : Matrix (Fin (a + b)) (Fin (a + b)) F)).toBlocks₂₁)
        (((z⁻¹ : GL (Fin b) F) : Matrix (Fin b) (Fin b) F) *
          (blk (p : Matrix (Fin (a + b)) (Fin (a + b)) F)).toBlocks₂₂ *
            (z : Matrix (Fin b) (Fin b) F)) := by
  have h1 : blk (((dg a z)⁻¹ : GL (Fin (a + b)) F) : Matrix (Fin (a + b)) (Fin (a + b)) F) =
      Matrix.fromBlocks 1 0 0 ((z⁻¹ : GL (Fin b) F) : Matrix (Fin b) (Fin b) F) := by
    ext i j
    simp [blk, dg, Units.inv_mk]
  have h2 : blk ((dg a z : GL (Fin (a + b)) F) : Matrix (Fin (a + b)) (Fin (a + b)) F) =
      Matrix.fromBlocks 1 0 0 (z : Matrix (Fin b) (Fin b) F) := by
    ext i j
    simp [blk, dg]
  rw [Units.val_mul, Units.val_mul, blk_mul, blk_mul, h1, h2,
    ← Matrix.fromBlocks_toBlocks (blk (p : Matrix (Fin (a + b)) (Fin (a + b)) F))]
  simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
    Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂, Matrix.fromBlocks_multiply]
  simp

private theorem toG_conj (z : GL (Fin b) F) (M : Matrix (Fin b) (Fin b) F) :
    toG (((z⁻¹ : GL (Fin b) F) : Matrix (Fin b) (Fin b) F) * M * (z : Matrix (Fin b) (Fin b) F)) =
      z⁻¹ * toG M * z := by
  by_cases h : IsUnit M
  · have h' : IsUnit (((z⁻¹ : GL (Fin b) F) : Matrix (Fin b) (Fin b) F) * M *
        (z : Matrix (Fin b) (Fin b) F)) :=
      ((Units.isUnit _).mul h).mul (Units.isUnit _)
    apply Units.ext
    simp [toG, h, h']
  · have h' : ¬ IsUnit (((z⁻¹ : GL (Fin b) F) : Matrix (Fin b) (Fin b) F) * M *
        (z : Matrix (Fin b) (Fin b) F)) := by
      intro hu
      apply h
      have : M = (z : Matrix (Fin b) (Fin b) F) *
          (((z⁻¹ : GL (Fin b) F) : Matrix (Fin b) (Fin b) F) * M * (z : Matrix (Fin b) (Fin b) F)) *
            ((z⁻¹ : GL (Fin b) F) : Matrix (Fin b) (Fin b) F) := by
        simp [mul_assoc]
      rw [this]
      exact ((Units.isUnit _).mul hu).mul (Units.isUnit _)
    simp [toG, h, h']

private theorem inPar_conj (z : GL (Fin b) F) (p : GL (Fin (a + b)) F) :
    InPar a ((dg a z)⁻¹ * p * dg a z) ↔ InPar a p := by
  rw [inPar_iff, inPar_iff, blk_conj, Matrix.toBlocks_fromBlocks₂₁]
  constructor
  · intro h
    have := congrArg (fun X => (z : Matrix (Fin b) (Fin b) F) * X) h
    simpa [← mul_assoc] using this
  · intro h
    rw [h]
    exact Matrix.mul_zero _

private theorem tlG_conj (z : GL (Fin b) F) (p : GL (Fin (a + b)) F) :
    tlG a ((dg a z)⁻¹ * p * dg a z) = tlG a p := by
  unfold tlG
  rw [tl_eq, tl_eq, blk_conj, Matrix.toBlocks_fromBlocks₁₁]

private theorem brG_conj (z : GL (Fin b) F) (p : GL (Fin (a + b)) F) :
    brG a b ((dg a z)⁻¹ * p * dg a z) = z⁻¹ * brG a b p * z := by
  unfold brG
  rw [br_eq, br_eq, blk_conj, Matrix.toBlocks_fromBlocks₂₂, toG_conj]

end Blocks

theorem resCl : ResCl := by
  intro F _ _ a b n hn T hT x y z
  subst hn
  unfold resT
  rw [← finsum_comp_equiv (MulAut.conj (dg a z)⁻¹).toEquiv]
  refine finsum_congr fun p => ?_
  have e : (MulAut.conj (dg a z)⁻¹).toEquiv p = (dg a z)⁻¹ * p * dg a z := by
    show (dg a z)⁻¹ * p * ((dg a z)⁻¹)⁻¹ = _
    rw [inv_inv]
  rw [e, inPar_conj, tlG_conj, brG_conj, hT]
  have : z⁻¹ * brG a b p * z = z⁻¹ * y * z ↔ brG a b p = y := by
    simp
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd ⟨h1.1, h1.2.1, this.1 h1.2.2⟩ h2
  · exact absurd ⟨h2.1, h2.2.1, this.2 h2.2.2⟩ h1
  · rfl

end UpperTheory.Gal.InertialTypesAlt
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PResDeg
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.resDeg :
    CardRes → ResDeg := by
  intro hcard K M _ _ _ _ _ _ hn v w hns hunr _
  classical
  have hw : (w : HeightOneSpectrum (𝓞 M)).asIdeal.LiesOver v.asIdeal := w.2
  set f := (w : HeightOneSpectrum (𝓞 M)).asIdeal.inertiaDeg (𝓞 K) with hf
  have hfconst : ∀ u : PlacesOver M v,
      (u : HeightOneSpectrum (𝓞 M)).asIdeal.inertiaDeg (𝓞 K) = f := by
    intro u
    haveI := u.2
    exact Ideal.inertiaDeg_eq_of_isGaloisGroup v.asIdeal _ _ Gal(M/K)
  have heone : ∀ u : PlacesOver M v,
      (u : HeightOneSpectrum (𝓞 M)).asIdeal.ramificationIdx (𝓞 K) = 1 := by
    intro u
    haveI := hunr u
    exact Ideal.ramificationIdx_eq_one _ _
  have hsum := GroundTheory.Global.SemiLocal.sum_ramificationIdx_mul_inertiaDeg M v
  have hdvd : f ∣ Module.finrank K M := by
    rw [← hsum]
    apply Finset.dvd_sum
    intro u _
    rw [heone u, hfconst u, one_mul]
  have hf1 : f ≠ 1 := by
    intro h1
    apply hns
    intro u
    haveI := u.2
    have hrk := GroundTheory.Global.SemiLocal.finrank_eq_ramificationIdx_mul_inertiaDeg M v
      (u : HeightOneSpectrum (𝓞 M))
    rw [heone u, hfconst u, h1, one_mul] at hrk
    have htop := Subalgebra.bot_eq_top_of_finrank_eq_one hrk
    intro y
    have hy : y ∈ (⊥ : Subalgebra (HeightOneSpectrum.adicCompletion K v)
        (HeightOneSpectrum.adicCompletion M (u : HeightOneSpectrum (𝓞 M)))) := by
      rw [htop]
      trivial
    obtain ⟨x, hx⟩ := Algebra.mem_bot.mp hy
    exact ⟨x, hx⟩
  have hfn : f = Module.finrank K M := (hn.eq_one_or_self_of_dvd f hdvd).resolve_left hf1
  have hnormK : normV v = v.asIdeal.absNorm := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  have hnormM : normV (w : HeightOneSpectrum (𝓞 M)) =
      (w : HeightOneSpectrum (𝓞 M)).asIdeal.absNorm := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  have hpow : v.asIdeal.absNorm ^ f = (w : HeightOneSpectrum (𝓞 M)).asIdeal.absNorm :=
    Ideal.absNorm_pow_inertiaDeg v.asIdeal _
  have hK := hcard K v
  have hM := hcard M (w : HeightOneSpectrum (𝓞 M))
  have hge : 2 ≤ v.asIdeal.absNorm := by
    have h0 : v.asIdeal.absNorm ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact v.ne_bot
    have h1 : v.asIdeal.absNorm ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]
      exact v.isPrime.ne_top
    omega
  have hcardM : Nat.card 𝓀[HeightOneSpectrum.adicCompletion M (w : HeightOneSpectrum (𝓞 M))] =
      Nat.card 𝓀[HeightOneSpectrum.adicCompletion K v] ^ Module.finrank K M := by
    rw [hM, hK, hnormM, hnormK, ← hpow, hfn]
  haveI : Finite 𝓀[HeightOneSpectrum.adicCompletion K v] :=
    Nat.finite_of_card_ne_zero (by rw [hK, hnormK]; omega)
  haveI : Finite 𝓀[HeightOneSpectrum.adicCompletion M (w : HeightOneSpectrum (𝓞 M))] :=
    Nat.finite_of_card_ne_zero (by rw [hcardM, hK, hnormK]; positivity)
  letI := Fintype.ofFinite 𝓀[HeightOneSpectrum.adicCompletion K v]
  haveI : Module.Finite 𝓀[HeightOneSpectrum.adicCompletion K v]
      𝓀[HeightOneSpectrum.adicCompletion M (w : HeightOneSpectrum (𝓞 M))] :=
    Module.Finite.of_finite
  refine ⟨?_, ?_⟩
  · have hc := Module.natCard_eq_pow_finrank (K := 𝓀[HeightOneSpectrum.adicCompletion K v])
      (V := 𝓀[HeightOneSpectrum.adicCompletion M (w : HeightOneSpectrum (𝓞 M))])
    rw [hcardM] at hc
    have h2 : 2 ≤ Nat.card 𝓀[HeightOneSpectrum.adicCompletion K v] := by
      rw [hK, hnormK]
      exact hge
    exact (Nat.pow_right_injective h2 hc).symm
  · refine ⟨FiniteField.frobeniusAlgEquivOfAlgebraic _ _, fun z => ?_⟩
    rw [FiniteField.frobeniusAlgEquivOfAlgebraic_apply, Nat.card_eq_fintype_card]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PResEmbCompat
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem pow_self_of_alg (k : Type) [Field k] [Finite k] (x : AlgebraicClosure k) :
    ∃ c : ℕ, 2 ≤ c ∧ x ^ c = x := by
  have hx : IsIntegral k x := Algebra.IsIntegral.isIntegral x
  haveI : FiniteDimensional k (IntermediateField.adjoin k {x}) := IntermediateField.adjoin.finiteDimensional hx
  haveI : Finite (IntermediateField.adjoin k {x}) := Module.finite_of_finite k
  haveI : Fintype (IntermediateField.adjoin k {x}) := Fintype.ofFinite _
  refine ⟨Fintype.card (IntermediateField.adjoin k {x}), Fintype.one_lt_card, ?_⟩
  have h := FiniteField.pow_card (⟨x, IntermediateField.mem_adjoin_simple_self k x⟩ : IntermediateField.adjoin k {x})
  exact congrArg Subtype.val h

private theorem exists_preimage {F F' R : Type} [Field F] [Field F'] [IsAlgClosed F'] [Field R]
    (e : F →+* R) (e' : F' →+* R) (h : ∀ x : F, ∃ c : ℕ, 2 ≤ c ∧ x ^ c = x) (x : F) :
    ∃ y, e' y = e x := by
  obtain ⟨c, hc, hx⟩ := h x
  have hmon : (X ^ c - X : Polynomial F').Monic := by
    apply monic_X_pow_sub
    rw [degree_X]
    exact_mod_cast (by omega : 1 < c)
  have hroots := hmon.roots_map_of_card_eq_natDegree e' IsAlgClosed.card_roots_eq_natDegree
  have hmem : e x ∈ ((X ^ c - X : Polynomial F').map e').roots := by
    rw [mem_roots (map_monic_ne_zero hmon)]
    simp only [IsRoot, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, eval_sub, eval_pow, eval_X]
    rw [← map_pow, hx, sub_self]
  rw [← hroots, Multiset.mem_map] at hmem
  obtain ⟨y, -, hy⟩ := hmem
  exact ⟨y, hy⟩

private theorem exists_equiv_of_fin {k k' R : Type} [Field k] [Field k'] [Finite k] [Finite k'] [Field R]
    (e : AlgebraicClosure k →+* R) (e' : AlgebraicClosure k' →+* R) :
    ∃ j : AlgebraicClosure k ≃+* AlgebraicClosure k', ∀ x, e' (j x) = e x := by
  have h1 : ∀ x, ∃ y, e' y = e x := fun x => exists_preimage e e' (pow_self_of_alg k) x
  have h2 : ∀ x, ∃ y, e y = e' x := fun x => exists_preimage e' e (pow_self_of_alg k') x
  have hr : e.range = e'.range := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨y, hy⟩ := h1 x
      exact ⟨y, hy⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨y, hy⟩ := h2 x
      exact ⟨y, hy⟩
  let φ := RingEquiv.ofBijective e.rangeRestrict
    ⟨fun a b hab => e.injective (congrArg Subtype.val hab), e.rangeRestrict_surjective⟩
  let ψ := RingEquiv.ofBijective e'.rangeRestrict
    ⟨fun a b hab => e'.injective (congrArg Subtype.val hab), e'.rangeRestrict_surjective⟩
  refine ⟨φ.trans ((RingEquiv.subringCongr hr).trans ψ.symm), fun x => ?_⟩
  have hq := ψ.apply_symm_apply ((RingEquiv.subringCongr hr) (φ x))
  exact congrArg Subtype.val hq

private theorem val_le_one_iff {k : Type} [Field k] [ValuativeRel k] {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (u : Valuation k Γ) (hu : (valuation k).IsEquiv u) (x : k) : x ∈ 𝒪[k] ↔ u x ≤ 1 := hu.le_one_iff_le_one

private theorem isUnit_iff_val {k : Type} [Field k] [ValuativeRel k] {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (u : Valuation k Γ) (hu : (valuation k).IsEquiv u) (x : 𝒪[k]) : IsUnit x ↔ u (x : k) = 1 := by
  exact (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.trans hu.eq_one_iff_eq_one

theorem UpperTheory.Gal.InertialTypesAlt.resEmbCompat :
    ResEmbCompat := by
  intro K M Ω _ _ _ _ _ _ _ _ _ A v w e e' he he'
  obtain ⟨j, hj⟩ := exists_equiv_of_fin e e'
  have eqv : (valuation (v.adicCompletion K)).IsEquiv Valued.v := ValuativeRel.isEquiv _ _
  have eqw : (valuation (w.1.adicCompletion M)).IsEquiv Valued.v := ValuativeRel.isEquiv _ _
  have he0 : w.1.asIdeal.ramificationIdx (𝓞 K) ≠ 0 := (Ideal.ramificationIdx_pos w.1.asIdeal (𝓞 K)).ne'
  let f : 𝒪[v.adicCompletion K] →+* 𝒪[w.1.adicCompletion M] :=
    (completionMap v w.1).comp (algebraMap 𝒪[v.adicCompletion K] (v.adicCompletion K)) |>.codRestrict
      (𝒪[w.1.adicCompletion M]) (fun x => by
        refine (val_le_one_iff _ eqw _).2 ?_
        change Valued.v (completionMap v w.1 x) ≤ 1
        rw [valued_completionMap]
        exact pow_le_one' ((val_le_one_iff _ eqv _).1 x.2) _)
  have hf : ∀ x, ((f x : 𝒪[w.1.adicCompletion M]) : w.1.adicCompletion M) = completionMap v w.1 x := fun _ => rfl
  haveI : IsLocalHom f := ⟨fun a ha => by
    rw [isUnit_iff_val _ eqw, hf, valued_completionMap] at ha
    rw [isUnit_iff_val _ eqv]
    exact (pow_eq_one_iff.1 ha).resolve_right he0⟩
  refine ⟨IsLocalRing.ResidueField.map f, j, fun x y hy => ?_, fun x => ?_, hj⟩
  · rw [IsLocalRing.ResidueField.map_residue]
    congr 1
    exact Subtype.ext hy
  · obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
    have hy1 : Valued.v (y : v.adicCompletion K) ≤ 1 := (val_le_one_iff _ eqv _).1 y.2
    obtain ⟨a, ha⟩ := DiscreteGroups.sglob.DzType.exists_int_approx_compl v (y : v.adicCompletion K) hy1
    have hb1 : Valued.v (algebraMap K (v.adicCompletion K) (a : K)) ≤ 1 := by
      have e2 : algebraMap K (v.adicCompletion K) (a : K) =
          (y : v.adicCompletion K) - ((y : v.adicCompletion K) - algebraMap K (v.adicCompletion K) (a : K)) := by ring
      rw [e2]
      exact (Valuation.map_sub _ _ _).trans (max_le hy1 ha.le)
    let b : 𝒪[v.adicCompletion K] := ⟨algebraMap K _ (a : K), (val_le_one_iff _ eqv _).2 hb1⟩
    have hyb : IsLocalRing.residue _ y = IsLocalRing.residue _ b := by
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        isUnit_iff_val _ eqv]
      exact ha.ne
    let a' : 𝓞 M := algebraMap (𝓞 K) (𝓞 M) a
    have ha' : (a' : M) = algebraMap K M (a : K) := rfl
    let z : A := ⟨algebraMap K Ω (a : K), mem_of_isIntegral_int A
      ((RingOfIntegers.isIntegral_coe a).map (IsScalarTower.toAlgHom ℤ K Ω))⟩
    have h1 := he a b z rfl rfl
    have h2 := he' a' (f b) z (by
      rw [hf, ha']
      change completionMap v w.1 (algebraMap K _ (a : K)) = _
      rw [completionMap_algebraMap]
      exact IsScalarTower.algebraMap_apply K M (w.1.adicCompletion M) _) (by
      rw [ha', ← IsScalarTower.algebraMap_apply])
    apply e'.injective
    rw [hj, hyb, h1, IsLocalRing.ResidueField.map_residue, h2]
end

