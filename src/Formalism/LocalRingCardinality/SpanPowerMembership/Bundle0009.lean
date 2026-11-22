import Formalism.LocalToGlobal.GroupLattices.FockModels.SwRowGenMonomial
import Lemmata.GeneralBFactRightBisForm.Imports
import Formalism.LocalRingCardinality.Bundle0002
import Formalism.LocalRingCardinality.Bundle0004
import Formalism.LocalRingCardinality.Bundle0003
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0005
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0008
import Formalism.LocalRingCardinality.SpanPowerMembership.UnitDivisorGood

-- bundled from Formalism.LocalRingCardinality.SpanPowerMembership.NZLevB
section
open MvPolynomial

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.GradedWeylDivisibility

section HW

variable (R : Type) [CommRing R] {r n : ℕ}

theorem rowAct_lpMinor (h : Matrix (Fin r) (Fin r) R) (hl : ∀ i j, i < j → h i j = 0) (s : ℕ) (hr : s ≤ r) (hn : s ≤ n) :
    rowAct R h (lpMinor R (n := n) s hr hn) =
      C (∏ a : Fin s, h (Fin.castLE hr a) (Fin.castLE hr a)) * lpMinor R s hr hn := by
  classical
  unfold lpMinor
  rw [AlgHom.map_det]
  have hM : (rowAct R (n := n) h).mapMatrix (Matrix.of fun p q : Fin s =>
      (X (Fin.castLE hr p, Fin.castLE hn q) : MvPolynomial (Fin r × Fin n) R)) =
      (Matrix.of fun p b : Fin s => (C (h (Fin.castLE hr p) (Fin.castLE hr b)) : MvPolynomial (Fin r × Fin n) R)) *
        Matrix.of fun p q : Fin s => (X (Fin.castLE hr p, Fin.castLE hn q) : MvPolynomial (Fin r × Fin n) R) := by
    refine Matrix.ext fun p q => ?_
    rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply]
    simp only [Matrix.of_apply]
    show rowAct R h (X (Fin.castLE hr p, Fin.castLE hn q)) = _
    rw [rowAct, aeval_X]
    symm
    refine Finset.sum_of_injOn (Fin.castLE hr) (Fin.castLE_injective hr).injOn (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
      (fun b _ hb => ?_) (fun _ _ => rfl)
    have hbs : ¬ b.val < s := fun hlt => hb ⟨⟨b.val, hlt⟩, Finset.mem_coe.mpr (Finset.mem_univ _), Fin.ext rfl⟩
    have : Fin.castLE hr p < b := by
      rw [Fin.lt_def, Fin.val_castLE]
      have := p.2
      omega
    rw [hl _ _ this, C_0, zero_mul]
  rw [hM, Matrix.det_mul, Matrix.det_of_lowerTriangular, map_prod]
  · rfl
  · intro i j hij
    have hij' : i < j := hij
    rw [Matrix.of_apply, hl _ _ (by rw [Fin.lt_def]; exact hij'), C_0]

def hwScal (hn : n ≤ r) (ν : Fin n → ℕ) (h : Matrix (Fin r) (Fin r) R) : R :=
  ∏ s : Fin n, (∏ a : Fin (s.val + 1), h (Fin.castLE (by omega) a) (Fin.castLE (by omega) a)) ^ (ν s - nuNext ν s)

theorem rowAct_hw (hn : n ≤ r) (ν : Fin n → ℕ) (h : Matrix (Fin r) (Fin r) R) (hl : ∀ i j, i < j → h i j = 0) :
    rowAct R h (hw R hn ν) = hwScal R hn ν h • hw R hn ν := by
  unfold hw hwScal
  rw [map_prod, smul_eq_C_mul, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_pow, rowAct_lpMinor R h hl, mul_pow, map_pow]

end HW

section ML

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ι → Type*} [∀ i, AddCommGroup (M i)]
  [∀ i, Module R (M i)] {A : Type*} [CommRing A] [Algebra R A]

theorem prod_mem_of_span (φ : ∀ i, M i →ₗ[R] A) (S : ∀ i, Set (M i)) (T : Submodule R A)
    (h : ∀ s : ∀ i, M i, (∀ i, s i ∈ S i) → ∏ i, φ i (s i) ∈ T) (m : ∀ i, M i)
    (hm : ∀ i, m i ∈ Submodule.span R (S i)) : ∏ i, φ i (m i) ∈ T := by
  first | exact Bl.general_b_fact_right_bis_form.goal1 .. | (apply Bl.general_b_fact_right_bis_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_right_bis_form.goal1 <;> assumption)

end ML

end Formalism.BasicNotions.Examples₂.NZ
end
end

-- bundled from Formalism.LocalRingCardinality.SpanPowerMembership.NZRowB
section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.BasicNotions

section Gen

variable {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
  [FiniteDimensional ℂ EE] (S : RowSide D EE)

theorem baseSubspace_top_of_identity {μ} (he : S.eOp μ = LinearMap.id) : S.V0 μ = ⊤ := by
  unfold RowSide.V0; rw [he]; exact LinearMap.range_id

theorem Usp_bot {μ} (he : S.eOp μ = LinearMap.id) (hi : Function.Injective (S.iota μ)) : S.Usp μ = ⊥ := by
  unfold RowSide.Usp; rw [baseSubspace_top_of_identity S he, LinearMap.ker_eq_bot.mpr hi, inf_bot_eq]

theorem Qsp_top {μ} (he : S.eOp μ = LinearMap.id) (hi : Function.Injective (S.iota μ)) : S.Qsp μ = ⊤ := by
  unfold RowSide.Qsp; rw [baseSubspace_top_of_identity S he, Usp_bot S he hi, Submodule.bot_orthogonal_eq_top, inf_top_eq]

theorem LamSet_eq {μ} (he : S.eOp μ = LinearMap.id) (hi : Function.Injective (S.iota μ)) :
    S.LamSet μ = (S.Mtilde μ).carrier := by
  unfold RowSide.LamSet
  have hp : ∀ x, (S.Qsp μ).starProjection x = x := fun x =>
    Submodule.starProjection_eq_self_iff.mpr (by rw [Qsp_top S he hi]; trivial)
  rw [baseSubspace_top_of_identity S he]
  ext x
  simp [hp]

theorem RRset_eq {μ} (he : S.eOp μ = LinearMap.id) (hi : Function.Injective (S.iota μ)) :
    S.RRset μ = S.iota μ '' (S.Mtilde μ).carrier := by
  unfold RowSide.RRset; rw [LamSet_eq S he hi]

theorem rrDef_of (Λ : Submodule (𝓞 D.what₂.LL) S.RR.V)
    (h : ∀ w y, S.jEE y ∈ S.RRset (D.what₂.muAt w) ↔ y ∈ Λ) (hL : S.RR.L = Λ) : S.RRDef := by
  intro x
  have hs : ∀ w, Submodule.span (𝓞 D.what₂.LL) {y | S.jEE y ∈ S.RRset (D.what₂.muAt w)} = Λ := fun w => by
    have : {y | S.jEE y ∈ S.RRset (D.what₂.muAt w)} = (Λ : Set S.RR.V) := Set.ext fun y => h w y
    rw [this, Submodule.span_eq]
  rw [hL]
  constructor
  · intro hx w
    exact ⟨1, fun h1 => (D.plEq w).isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1), by
      rw [one_smul, hs]; exact hx⟩
  · intro hx
    refine mem_of_local Λ x fun P hP => ?_
    have hne : P ≠ ⊥ := fun hb => RingOfIntegers.not_isField D.what₂.LL
      (Ring.isField_iff_maximal_bot.mpr (hb ▸ hP))
    obtain ⟨d, hd, hdx⟩ := hx (D.plEq.symm ⟨P, hP.isPrime, hne⟩)
    rw [hs] at hdx
    rw [Equiv.apply_symm_apply] at hd
    exact ⟨d, hd, hdx⟩

end Gen

structure CentralCharacterOne (D : D7) where
  χ : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) →ₐ[ℂ] ℂ
  cen : D.ntypes.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))
  one : χ ⟨D.ntypes.e0, cen⟩ = 1

section Std

variable (D : D7) (c : CentralCharacterOne D) {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
  [FiniteDimensional ℂ EE] {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ EE)

def stdSide : RowSide D EE where
  Amb := fun _ => EE
  Mult := fun _ _ => EE
  multZero := fun _ => LinearIsometryEquiv.refl ℂ EE
  multTop := fun _ => LinearIsometryEquiv.refl ℂ EE
  io := fun _ _ => LinearMap.id
  Mtilde := fun _ => oB b _
  cen := fun _ => (Algebra.ofId ℂ (Module.End ℂ EE)).comp c.χ
  eOp := fun _ => LinearMap.id
  eOp_idem := fun _ => rfl
  eOp_sa := fun _ _ _ => rfl
  eOp_tie := fun _ => by
    rw [dif_pos c.cen]
    show LinearMap.id = algebraMap ℂ (Module.End ℂ EE) (c.χ ⟨D.ntypes.e0, c.cen⟩)
    rw [c.one, map_one]; rfl
  RR := stdH D.what₂.LL n
  RR_frames := stdH_frames _ n
  jEE := jB D.what₂.embLL b
  jEE_basis := jB_basis _ b
  jEE_norm := jB_norm _ b

theorem stdSide_downTo (μ) (j : ℕ) : (stdSide D c b).downTo μ j = LinearMap.id := by
  induction j with
  | zero => rfl
  | succ j ih => show ((stdSide D c b).downTo μ j).comp LinearMap.id = _; rw [ih]; rfl

theorem stdSide_iota (μ) : (stdSide D c b).iota μ = LinearMap.id := by
  show (LinearMap.id : EE →ₗ[ℂ] EE) ∘ₗ (stdSide D c b).downTo μ D.R.m ∘ₗ (LinearMap.id : EE →ₗ[ℂ] EE) = _
  rw [stdSide_downTo]; rfl

end Std

theorem jB_mem_oB {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) {n : ℕ}
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (b : OrthonormalBasis (Fin n) ℂ V)
    {O : Type} [CommRing O] (f : O →+* K) (hf : ∀ z : K, (∃ y, f y = z) ↔ ∃ c : 𝓞 K, z = (c : K))
    (x : Fin n → K) : jB σ b x ∈ (oB b (σ.comp f)).carrier ↔ x ∈ (stdH K n).L := by
  rw [mem_oB, mem_stdL]
  constructor
  · rintro ⟨c, hc⟩ i
    refine (hf (x i)).mp ⟨c i, σ.injective ?_⟩
    have h2 : (∑ k, (σ.comp f) (c k) • b k) = jB σ b (fun k => f (c k)) := rfl
    have h1 := congrArg (fun y => b.repr y i) hc
    simp only [h2, repr_jB] at h1
    exact h1.symm
  · intro h
    have h' := fun i => (hf (x i)).mpr (h i)
    choose c hc using h'
    exact ⟨c, by rw [jB_apply]; exact Finset.sum_congr rfl fun i _ => by rw [RingHom.comp_apply, hc i]⟩

def OFull (D : D7) : Prop := ∀ z : D.what₂.LL, (∃ y, D.what₂.OtoLL y = z) ↔ ∃ c : 𝓞 D.what₂.LL, z = (c : D.what₂.LL)

section Std2

variable (D : D7) (c : CentralCharacterOne D) (hO : OFull D) {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
  [FiniteDimensional ℂ EE] {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ EE)

include hO in
theorem stdSide_rrDef : (stdSide D c b).RRDef := by
  refine rrDef_of _ (stdH D.what₂.LL n).L (fun w y => ?_) rfl
  rw [RRset_eq _ rfl (by rw [stdSide_iota]; exact Function.injective_id), stdSide_iota]
  have e : (⇑(LinearMap.id : EE →ₗ[ℂ] EE)) '' ((stdSide D c b).Mtilde (D.what₂.muAt w)).carrier =
      (oB b (D.what₂.embLL.comp D.what₂.OtoLL)).carrier := Set.image_id _
  exact (iff_of_eq (congrArg (fun s => jB D.what₂.embLL b y ∈ s) e)).trans
    (jB_mem_oB D.what₂.embLL b D.what₂.OtoLL hO y)

theorem stdSide_rrFull : (stdSide D c b).RRFull := (stdH_good D.what₂.LL n).2

def ambOf (S : RowSide D EE) (m : D.what₂.Tup → ℕ) (bA : ∀ μ, OrthonormalBasis (Fin (m μ)) ℂ (S.Amb μ))
    (hg : ∀ μ, (S.Mtilde μ).gen = genB (bA μ)) : AmbForm D S where
  MtH := fun μ => stdH D.what₂.LL (m μ)
  jAmb := fun μ => jB D.what₂.embLL (bA μ)
  MtH_good := fun μ _ => stdH_good _ _
  jAmb_basis := fun μ _ => jB_basis _ _
  jAmb_lat := fun μ _ x => by rw [hg]; exact jB_lat _ _ x
  jAmb_gen := fun μ _ => by rw [hg]; exact jB_gen _ _
  jAmb_norm := fun μ _ => jB_norm _ _

def standardBaseSide : BaseLevelRowSide D := ⟨stdSide D c D.what₂.onb0⟩

include hO in
theorem standardBaseSide_latticeDefined : (standardBaseSide D c).s.RRDef := stdSide_rrDef D c hO _

def standardAmbientForm : AmbForm D (standardBaseSide D c).s := ambOf D _ (fun _ => D.what₂.D0) (fun _ => D.what₂.onb0) (fun _ => rfl)

end Std2

end Formalism.BasicNotions.Examples₂.NZ
end
end

-- bundled from Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeL
section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.BasicNotions NumberField IsDedekindDomain Polynomial

attribute [local instance] neZero_g fact_g Classical.propDecidable

variable {R : Ranks} (H : Host R)

def etaZ (k : Fin 2) : GL (Fin R.r) (ZMod (H.g k)) →* ℤˣ :=
  (quadraticChar (ZMod (H.g k))).toUnitHom.comp Matrix.GeneralLinearGroup.det

theorem exists_etaZ (ht : THyp H) (k : Fin 2) : ∃ x, etaZ H k x = -1 := by
  have hc : ringChar (ZMod (H.g k)) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact (ht.jac k).1
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' hc
  have hr : 0 < R.r := Nat.pos_of_ne_zero (r_ne_zero R)
  let M : Matrix (Fin R.r) (Fin R.r) (ZMod (H.g k)) :=
    Matrix.diagonal (Function.update (fun _ => 1) (⟨0, hr⟩ : Fin R.r) (a : ZMod (H.g k)))
  have hdet : M.det = a := by
    rw [Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ _)]
    simp
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hdet]; exact a.ne_zero), Units.ext ?_⟩
  show quadraticChar (ZMod (H.g k)) (Matrix.det M) = -1
  rw [hdet, ha]

variable (K : Type) [Field K] [CharZero K]

def psiU (k : Fin 2) (v : Fin R.f) : GL (Fin R.r) (ZMod (H.g k)) →* Kˣ :=
  if v.1 ≠ 0 then (Units.map (Int.castRingHom K).toMonoidHom).comp (etaZ H k) else 1

variable (Lb : Lbl H) (what₂ : Rows.Data R) (h : NHyp H what₂)

def PsiU : G0g (ndG H Lb what₂ h) →* Kˣ :=
  ∏ kv : Ix (ndG H Lb what₂ h), (psiU H K kv.1 kv.2).comp (Pi.evalMonoidHom _ kv)

theorem PsiU_apply (g : G0g (ndG H Lb what₂ h)) :
    ((PsiU H K Lb what₂ h g : Kˣ) : K) = ∏ kv : Ix (ndG H Lb what₂ h), ((psiU H K kv.1 kv.2 (g kv) : Kˣ) : K) := by
  unfold PsiU
  rw [MonoidHom.finsetProd_apply, Units.coe_prod]
  rfl

theorem monicOf_eq_iff {k : Fin 2} (f : (ZMod (H.g k))[X]) (hm : f.Monic) (hd : f.natDegree = R.r)
    (a : Fin R.r → ZMod (H.g k)) : Formalism.CyclotomicNorms.monicOf a = f ↔ a = fun i : Fin R.r => f.coeff i := by
  constructor
  · intro e
    funext i
    rw [← e, Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt]
  · intro e
    rw [e]
    exact Formalism.CyclotomicNorms.Sqf.monicOf_coeffs f hm hd

theorem evS_eSum' {K : Type} [Field K] {I : Type} [Fintype I] [dI : DecidableEq I] {G : I → Type} [∀ i, Group (G i)]
    [∀ i, Finite (G i)] {L : I → Type} [∀ i, Fintype (L i)] (E : ∀ i, L i → MonoidAlgebra K (G i))
    (S : (∀ i, L i) → Prop) (ψ : ∀ i, G i → K) (b : ∀ i, L i) (hb : S b)
    (h1 : ∀ i, evS (ψ i) (E i (b i)) = 1) (h0 : ∀ i l, l ≠ b i → evS (ψ i) (E i l) = 0) :
    evS (fun g : ∀ i, G i => ∏ i, ψ i (g i)) (@eSum K _ I _ G _ _ L _ dI E S) = 1 := by
  unfold eSum
  rw [evS_sum, Finset.sum_eq_single b]
  · rw [if_pos hb, evS_tens]
    exact Finset.prod_eq_one fun i _ => h1 i
  · intro a _ hab
    split_ifs
    · rw [evS_tens]
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hab
      exact Finset.prod_eq_zero (Finset.mem_univ i) (h0 i _ hi)
    · exact evS_zero _
  · intro h; exact absurd (Finset.mem_univ _) h

omit [CharZero K] in

theorem evS_e0F {what₂ : Rows.Data R} (N : NData R H what₂)
    (es : ∀ k, (ZMod (H.g k))[X] → MonoidAlgebra K (GL (Fin R.r) (ZMod (H.g k))))
    (ψ : ∀ kv : Ix N, GL (Fin R.r) (ZMod (H.g kv.1)) → K) (f : ∀ k, N.PlG k → (ZMod (H.g k))[X]) (hf : GoodT N f)
    (hδ : ∀ (kv : Ix N) (p : (ZMod (H.g kv.1))[X]), evS (ψ kv) (es kv.1 p) = if p = f kv.1 kv.2 then 1 else 0) :
    evS (fun g : G0g N => ∏ kv, ψ kv (g kv)) (e0F N es) = 1 := by
  have hm : ∀ k v, Formalism.CyclotomicNorms.monicOf (fun i : Fin R.r => (f k v).coeff i) = f k v := fun k v =>
    Formalism.CyclotomicNorms.Sqf.monicOf_coeffs _ ((hf k).1.1 v).1 ((hf k).1.1 v).2.1
  have hb : GoodT N (fun k v => Formalism.CyclotomicNorms.monicOf (fun i : Fin R.r => (f k v).coeff i)) := by
    have : (fun k v => Formalism.CyclotomicNorms.monicOf (fun i : Fin R.r => (f k v).coeff i)) = f :=
      funext fun k => funext fun v => hm k v
    rw [this]; exact hf
  have hd1 : ∀ kv : Ix N, evS (ψ kv) (es kv.1 (Formalism.CyclotomicNorms.monicOf fun i : Fin R.r => (f kv.1 kv.2).coeff i)) = 1 :=
    fun kv => by rw [hδ, if_pos (hm _ _)]
  have hd0 : ∀ (kv : Ix N) (a : Fin R.r → ZMod (H.g kv.1)), a ≠ (fun i : Fin R.r => (f kv.1 kv.2).coeff i) →
      evS (ψ kv) (es kv.1 (Formalism.CyclotomicNorms.monicOf a)) = 0 := fun kv a e => by
    rw [hδ, if_neg (fun e' => e ((monicOf_eq_iff H _ ((hf kv.1).1.1 kv.2).1 ((hf kv.1).1.1 kv.2).2.1 a).mp e'))]
  exact evS_eSum' (I := Ix N) (G := fun kv => GL (Fin R.r) (ZMod (H.g kv.1)))
    (L := fun kv => Fin R.r → ZMod (H.g kv.1)) (fun kv a => es kv.1 (Formalism.CyclotomicNorms.monicOf a))
    (fun a => GoodT N fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) ψ
    (fun kv => fun i : Fin R.r => (f kv.1 kv.2).coeff i) hb hd1 hd0

theorem evS_e0L (ht : THyp H) :
    evS (fun g => ((PsiU H K Lb what₂ h g : Kˣ) : K)) (e0L H Lb what₂ h K) = 1 := by
  have e : (fun g => ((PsiU H K Lb what₂ h g : Kˣ) : K)) =
      fun g : G0g (ndG H Lb what₂ h) => ∏ kv : Ix (ndG H Lb what₂ h), ((psiU H K kv.1 kv.2 (g kv) : Kˣ) : K) :=
    funext fun g => PsiU_apply H K Lb what₂ h g
  rw [e]
  refine evS_e0F H K (ndG H Lb what₂ h) (esL Lb K) (fun kv x => ((psiU H K kv.1 kv.2 x : Kˣ) : K)) (tupL Lb)
    (goodT_tupL H Lb what₂ h) ?_
  rintro ⟨k, v⟩ p
  have hv' : (v : Fin R.f).1 ≠ 0 ∨ (v : Fin R.f).1 = 0 := (em _).symm
  show evS (fun x => ((psiU H K k v x : Kˣ) : K)) (esZ K _ (Lb.fA k) (Lb.fB k) p) = if p = tupL Lb k v then 1 else 0
  rcases hv' with hv | hv
  · obtain ⟨x, hx⟩ := exists_etaZ H ht k
    have hψ : (fun y => ((psiU H K k v y : Kˣ) : K)) =
        ⇑((Units.coeHom K).comp ((Units.map (Int.castRingHom K).toMonoidHom).comp (etaZ H k))) := by
      funext y; unfold psiU; rw [if_pos hv]; rfl
    rw [hψ, evS_esZ_ne (Lb.ne k) _ x (by
      show (((etaZ H k x : ℤˣ) : ℤ) : K) ≠ 1
      rw [hx]; norm_num)]
    have ht' : tupL Lb k v = Lb.fA k := by unfold tupL; rw [if_pos (by simpa using hv)]
    rw [ht']
    split_ifs <;> rfl
  · have hψ : (fun y => ((psiU H K k v y : Kˣ) : K)) = fun _ => 1 := by
      funext y; unfold psiU; rw [if_neg (not_not.mpr hv)]; rfl
    rw [hψ, evS_esZ_one (Lb.ne k)]
    have ht' : tupL Lb k v = Lb.fB k := by unfold tupL; rw [if_neg (by simpa using hv)]
    rw [ht']
    split_ifs <;> rfl

variable (V : Type) [AddCommGroup V] [Module K V]

def actGL : G0g (ndG H Lb what₂ h) →* (V ≃ₗ[K] V) where
  toFun g := LinearEquiv.smulOfUnit (PsiU H K Lb what₂ h g)
  map_one' := by
    ext x
    show PsiU H K Lb what₂ h 1 • x = x
    rw [map_one, one_smul]
  map_mul' a b := by
    ext x
    show PsiU H K Lb what₂ h (a * b) • x = PsiU H K Lb what₂ h a • PsiU H K Lb what₂ h b • x
    rw [map_mul, mul_smul]

theorem lift_actGL (ht : THyp H) :
    MonoidAlgebra.lift K (Module.End K V) (G0g (ndG H Lb what₂ h))
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (actGL H K Lb what₂ h V)) (e0L H Lb what₂ h K) = 1 := by
  rw [lift_scalar ((Units.coeHom K).comp (PsiU H K Lb what₂ h)) _ (fun g => by ext x; rfl)]
  show evS (fun g => ((PsiU H K Lb what₂ h g : Kˣ) : K)) _ • (1 : Module.End K V) = 1
  rw [evS_e0L H K Lb what₂ h ht, one_smul]

end Formalism.BasicNotions.Examples₂.NZ
end
end

-- bundled from Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeO
section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.BasicNotions NumberField IsDedekindDomain Polynomial

attribute [local instance] neZero_g fact_g Classical.propDecidable

variable {R : Ranks} (H : Host R) (Lb : Lbl H) (what₂ : Rows.Data R) (h : NHyp H what₂)

theorem labelIdempotent_ne_one (ht : THyp H) : e0L H Lb what₂ h ℂ ≠ 1 := by
  intro e1
  let b : ∀ kv : Ix (ndG H Lb what₂ h), Fin R.r → ZMod (H.g kv.1) := fun kv => fun i => (Lb.fA kv.1).coeff i
  have hm : ∀ k, Formalism.CyclotomicNorms.monicOf (fun i : Fin R.r => (Lb.fA k).coeff i) = Lb.fA k := fun k =>
    Formalism.CyclotomicNorms.Sqf.monicOf_coeffs _ (Lb.okA k).1 (Lb.okA k).2.1
  have hS : ¬ GoodT (ndG H Lb what₂ h) (fun k v => Formalism.CyclotomicNorms.monicOf (b ⟨k, v⟩)) := by
    intro hg
    have := (hg 0).1
    simp only [b, hm] at this
    exact ND.not_isGood_const _ _ this
  have hmul := eSum_mul_tens (I := Ix (ndG H Lb what₂ h)) (G := fun kv => GL (Fin R.r) (ZMod (H.g kv.1)))
    (L := fun kv => Fin R.r → ZMod (H.g kv.1)) (fun kv a => esL Lb ℂ kv.1 (Formalism.CyclotomicNorms.monicOf a))
    (fun a => GoodT (ndG H Lb what₂ h) fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩))
    (fun kv l => esZ_idem _) (fun kv l l' hl => esZ_orth _ _ (monicOf_injective.ne hl)) b
  rw [if_neg hS] at hmul
  have hne : tens (fun kv : Ix (ndG H Lb what₂ h) => esL Lb ℂ kv.1 (Formalism.CyclotomicNorms.monicOf (b kv))) ≠ 0 :=
    tens_ne_zero _ fun kv => by
      show esZ ℂ _ (Lb.fA kv.1) (Lb.fB kv.1) (Formalism.CyclotomicNorms.monicOf fun i : Fin R.r => (Lb.fA kv.1).coeff i) ≠ 0
      rw [hm]
      unfold esZ
      rw [if_pos rfl]
      exact one_sub_eT_ne_zero (zL H kv.1) (zL_ne_one H ht kv.1)
  apply hne
  have : e0L H Lb what₂ h ℂ = eSum (I := Ix (ndG H Lb what₂ h)) (G := fun kv => GL (Fin R.r) (ZMod (H.g kv.1)))
      (L := fun kv => Fin R.r → ZMod (H.g kv.1)) (fun kv a => esL Lb ℂ kv.1 (Formalism.CyclotomicNorms.monicOf a))
      (fun a => GoodT (ndG H Lb what₂ h) fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) := rfl
  rw [← this, e1, one_mul] at hmul
  exact hmul

theorem one_sub_e0L_mem_center :
    1 - e0L H Lb what₂ h ℂ ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (ndG H Lb what₂ h))) :=
  Subalgebra.sub_mem _ (Subalgebra.one_mem _) (labelIdempotent_mem_center H Lb what₂ h)

def labelComplementCharacter (ht : THyp H) : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (ndG H Lb what₂ h))) →ₐ[ℂ] ℂ :=
  (exists_char _ (one_sub_e0L_mem_center H Lb what₂ h)
    (by rw [sub_mul, mul_sub, mul_sub, labelIdempotent_idem, one_mul, one_mul, mul_one, sub_self, sub_zero])
    (sub_ne_zero.mpr (labelIdempotent_ne_one H Lb what₂ h ht).symm)).choose

theorem labelComplementCharacter_idempotent_zero (ht : THyp H) : labelComplementCharacter H Lb what₂ h ht ⟨e0L H Lb what₂ h ℂ, labelIdempotent_mem_center H Lb what₂ h⟩ = 0 := by
  have h1 : labelComplementCharacter H Lb what₂ h ht ⟨1 - e0L H Lb what₂ h ℂ, one_sub_e0L_mem_center H Lb what₂ h⟩ = 1 :=
    (exists_char _ (one_sub_e0L_mem_center H Lb what₂ h)
      (by rw [sub_mul, mul_sub, mul_sub, labelIdempotent_idem, one_mul, one_mul, mul_one, sub_self, sub_zero])
      (sub_ne_zero.mpr (labelIdempotent_ne_one H Lb what₂ h ht).symm)).choose_spec
  have e : (⟨1 - e0L H Lb what₂ h ℂ, one_sub_e0L_mem_center H Lb what₂ h⟩ :
      Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (ndG H Lb what₂ h)))) = 1 - ⟨_, labelIdempotent_mem_center H Lb what₂ h⟩ := rfl
  rw [e, map_sub, map_one] at h1
  linear_combination -h1

end Formalism.BasicNotions.Examples₂.NZ
end
end

