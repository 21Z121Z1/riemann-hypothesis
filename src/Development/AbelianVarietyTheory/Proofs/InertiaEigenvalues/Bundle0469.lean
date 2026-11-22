import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAuxiliaryPrimesPrescribedFrobenius
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0014
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0439
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0411
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0420
import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0442
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0421
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0444
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNewPlaceFrobeniusConjugateModOpenNormalSub
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
open GlobalTheory.ChosenPrimes

namespace GlobalTheory.NewPrimePick

theorem exists_newPlace : Cheb → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (s : X.Sig i), ∀ (M R n : ℕ) (d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (A₀ : Finset (PlE D.host)) (L : Subgroup (GE N)) (z : GE N) (P : Fin R ⊕ Fin n → PlE D.host), 1 ≤ M → IsTameInertiaElementAtTwistPrime X i z → Small2 i s M L z → PiLocalization₂ i M d A₀ L z P → n < R → ∀ (H : Subgroup (GE N)) (S : Finset (PlE D.host)), AdmFam X i M H S d → L ≤ H → ∀ (U : Subgroup (GE N)) (h : GE N), IsOpen (U : Set (GE N)) → U.Normal → U ≤ L → h ∈ L → (∀ b : Fin R, b.val < n → d (P (.inl b)) h = 1) → (∀ b : Fin R, n ≤ b.val → Ine (F := D.host.E) (N.plOm.1 (P (.inl b))) ≤ U) → ∃ P' : Fin R ⊕ Fin (n + 1) → PlE D.host, Ext P P' ∧ PiLocalization₂ i M d A₀ L z P' ∧ ∃ σ γ g : GE N, NewPl i M L (P' (.inr (Fin.last n))) (d (P' (.inr (Fin.last n)))) σ γ ∧ d (P' (.inr (Fin.last n))) σ = 1 ∧ g * σ * g⁻¹ * h⁻¹ ∈ U := by
  intro hC D N X i s M R n d A L z P _ _ hsm hst _ H S hA hLH U h hU hUn hUL hh hh1 hIU
  classical
  obtain ⟨-, -, -, hd⟩ := hA
  obtain ⟨⟨hL, hLn, -⟩, hLr, -⟩ := hsm
  obtain ⟨⟨ha1, ha2, ha3⟩, hs1, hs2⟩ := hst
  have hl := (X.lPrime i).out
  set m := 2 * X.l i ^ M with hm
  have hn1 : 1 < m := by have := Nat.pow_pos (n := M) hl.pos; omega
  have hn0 : m ≠ 0 := by omega
  have hval := exists_values (U ⊓ ⨅ b : {b : Fin R // b.val < n}, (d (P (.inl b.1))).ker)
    (fun b : {b : Fin R // n ≤ b.val} => d (P (.inl b.1))) (fun b c => by
      obtain ⟨γ, hγ, e⟩ := (ha3 (.inl b.1)).2.2.2.2 _ (over_refl _) _ (N.plOm.2 (P (.inl b.1))) c
      have key : ∀ b' : Fin R, b' ≠ b.1 → d (P (.inl b')) γ = 1 := fun b' hb' =>
        (ha3 (.inl b')).2.2.2.1 _ (fun h => hb' (Sum.inl_injective (ha2 _ _ h))) _ (N.plOm.2 (P (.inl b.1))) γ hγ
      refine ⟨γ, ⟨hIU b.1 b.2 hγ, Subgroup.mem_iInf.2 fun b' => key b'.1 fun h => ?_⟩, e,
        fun b' hb' => key b'.1 fun h => hb' (Subtype.ext h)⟩
      have h1 := b'.2
      have h2 := b.2
      rw [h] at h1
      omega)
  obtain ⟨γ₀, hγ₀, hγd⟩ := hval fun b =>
    Multiplicative.ofAdd (if n = b.1.val then 1 else 0) * (d (P (.inl b.1)) h)⁻¹
  have hγh : ∀ b : Fin R, d (P (.inl b)) (γ₀ * h) = Multiplicative.ofAdd (if n = b.val then 1 else 0) := by
    intro b
    rw [map_mul]
    rcases lt_or_ge b.val n with hb | hb
    · have h1 : d (P (.inl b)) γ₀ = 1 := Subgroup.mem_iInf.1 hγ₀.2 ⟨b, hb⟩
      rw [h1, hh1 b hb, if_neg (by omega), mul_one]
      rfl
    · rw [hγd ⟨b, hb⟩, inv_mul_cancel_right]
  let V : Subgroup (GE N) := U ⊓ ⨅ b, (d (P (.inl b))).ker
  have hV : IsOpen (V : Set (GE N)) := by
    refine hU.inter ?_
    show IsOpen ((⨅ b, (d (P (.inl b))).ker : Subgroup (GE N)) : Set (GE N))
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun b => (ha3 (.inl b)).1
  have hVn : V.Normal := by
    have : (⨅ b, (d (P (.inl b))).ker).Normal := Subgroup.normal_iInf_normal fun b => inferInstance
    infer_instance
  obtain ⟨T₀, hT₀, hsp⟩ := GlobalTheory.FrobDense.exists_finite_split D.host
  let T : Set (PlE D.host) := ((↑A ∪ ↑S ∪ ↑(X.S0 i)) ∪ (T₀ ∪ {P | P.asIdeal.ramificationIdx ℤ ≠ 1}) ∪
    ({v | ((m : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal} ∪
      {v | ∃ B : ValuationSubring N.Om, IsPlaceOver B v ∧ ¬ Ine (F := D.host.E) B ≤ U})) ∪ Set.range P
  have hT : T.Finite :=
    ((((A.finite_toSet.union S.finite_toSet).union (X.S0 i).finite_toSet).union
      (hT₀.union (GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified D.host.E).2)).union
      ((finite_mem hn0).union (finite_ram hU))).union (Set.finite_range P)
  obtain ⟨p, hp⟩ := exists_pick hC hV hVn (γ₀ * h) hT
  have h1 : ∀ v, Over p v → ((((v ∉ A ∧ v ∉ S) ∧ v ∉ X.S0 i) ∧ v ∉ T₀ ∧ v.asIdeal.ramificationIdx ℤ = 1) ∧
      ((m : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal ∧
      ∀ B : ValuationSubring N.Om, IsPlaceOver B v → Ine (F := D.host.E) B ≤ U) ∧ v ∉ Set.range P := fun v hv => by
    have : v ∉ T := (hp.1 v hv).1
    simpa only [T, Set.mem_union, not_or, Finset.mem_coe, Set.mem_ofPred_eq, not_exists, not_and, not_not] using this
  obtain ⟨σ, hσ⟩ := exists_isFrob (N.plOm.2 p)
  obtain ⟨k, hk⟩ := hp.2 σ hσ
  have hσL : σ ∈ L := by
    have h2 := hLn.conj_mem _ (L.mul_mem (hUL hk.1) (L.mul_mem (hUL hγ₀.1) hh)) k⁻¹
    have e : k⁻¹ * (k * σ * k⁻¹ * (γ₀ * h)⁻¹ * (γ₀ * h)) * k⁻¹⁻¹ = σ := by group
    rwa [e] at h2
  have hP0 := h1 p (over_refl p)
  have hq := norm_mod (N.plOm.2 p) hn1 hP0.1.2.1 hσ (hLr σ hσL)
  have hIp : Ine (F := D.host.E) (N.plOm.1 p) ≤ U := hP0.1.2.2 _ (N.plOm.2 p)
  have hdec : DecV N p ≤ L := dec_le (N.plOm.2 p) hL (hIp.trans hUL) hσ hσL
  have hspl : IsSplitPl D.host p := hsp p hP0.1.1.2.1 (hp.1 p (over_refl p)).2
  have hgood : GoodChar X i M p (d p) := hd p hP0.1.1.1.1.2 hspl (hdec.trans hLH)
  have haux : ∀ v, Over p v → IsSplitPl D.host v ∧ v.asIdeal.inertiaDeg ℤ = 1 ∧ Formalism.BasicNotions.eWL D.host.E v = 1 ∧
      v ∉ X.S0 i ∧ v ∉ A ∧ normV v % m = 1 := by
    refine fun v hv => ⟨hsp v (h1 v hv).1.1.2.1 (hp.1 v hv).2, (hp.1 v hv).2, (h1 v hv).1.1.2.2, (h1 v hv).1.1.1.2,
      (h1 v hv).1.1.1.1.1, ?_⟩
    rcases hv with rfl | hv
    · exact hq
    · rwa [normV_conj hv]
  let P' : Fin R ⊕ Fin (n + 1) → PlE D.host :=
    Sum.elim (fun a => P (.inl a)) (Fin.snoc (α := fun _ => PlE D.host) (fun a => P (.inr a)) p)
  have e1 : P' (.inr (Fin.last n)) = p := by simp [P']
  have e2 : ∀ q, P' (Sum.map id Fin.castSucc q) = P q := by
    rintro (a | a) <;> simp [P']
  have cases : ∀ q : Fin R ⊕ Fin (n + 1), q = .inr (Fin.last n) ∨ ∃ q₀, q = Sum.map id Fin.castSucc q₀ := by
    rintro (a | a)
    · exact Or.inr ⟨.inl a, rfl⟩
    · refine Fin.lastCases (Or.inl rfl) (fun a => Or.inr ⟨.inr a, rfl⟩) a
  refine ⟨P', e2, ⟨⟨fun q => ?_, fun q q' => ?_, fun q => ?_⟩, hs1, fun a => ?_⟩, ?_⟩
  · rcases cases q with rfl | ⟨q, rfl⟩
    · rw [e1]; exact haux
    · rw [e2]; exact ha1 q
  · rcases cases q with rfl | ⟨q, rfl⟩ <;> rcases cases q' with rfl | ⟨q', rfl⟩
    · exact fun _ => rfl
    · rw [e1, e2]; exact fun h => ((h1 _ h).2 ⟨q', rfl⟩).elim
    · rw [e1, e2]; exact fun h => ((h1 _ (over_symm h)).2 ⟨q, rfl⟩).elim
    · rw [e2, e2]; exact fun h => by rw [ha2 _ _ h]
  · show GoodChar X i M (P' q) (d (P' q))
    rcases cases q with rfl | ⟨q, rfl⟩
    · rw [e1]; exact hgood
    · rw [e2]; exact ha3 q
  · refine Fin.lastCases ?_ (fun a => ?_) a
    · rw [e1]
      refine ⟨hdec, fun b τ hτ => ?_⟩
      obtain ⟨k', hk'⟩ := hp.2 τ hτ
      have h2 : d (P (.inl b)) _ = 1 := Subgroup.mem_iInf.1 hk'.2 b
      rw [map_mul, map_inv, hγh] at h2
      simp only [map_mul, map_inv, mul_inv_cancel_comm, mul_inv_eq_one] at h2
      exact h2
    · have e3 : P' (.inr a.castSucc) = P (.inr a) := e2 (.inr a)
      rw [e3]
      exact hs2 a
  · rw [e1]
    obtain ⟨γ, hγ, hγ1⟩ := hgood.2.2.2.2 p (over_refl p) _ (N.plOm.2 p) (Multiplicative.ofAdd 1)
    obtain ⟨τ, hτ, hτ1⟩ := hgood.2.2.2.2 p (over_refl p) _ (N.plOm.2 p) (d p σ)⁻¹
    refine ⟨σ * τ, γ, k, ⟨fun v hv => (haux v hv).2.2.2.1, hspl, hq, hdec, hgood.1, ?_, hγ, hγ1⟩, ?_, ?_⟩
    · first | exact isFrob_mul_of_mem_Ine hσ hτ | exact isFrob_mul_of_mem_Ine hτ hσ
    · rw [map_mul, hτ1, mul_inv_cancel]
    · have h2 := U.mul_mem (U.mul_mem (hUn.conj_mem _ (hIp hτ) (k * σ)) hk.1) hγ₀.1
      have e : k * σ * τ * (k * σ)⁻¹ * (k * σ * k⁻¹ * (γ₀ * h)⁻¹) * γ₀ = k * (σ * τ) * k⁻¹ * h⁻¹ := by group
      rwa [e] at h2

end GlobalTheory.NewPrimePick
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOrthogonalIdempotentsHeckeSpanRep
section
noncomputable section

namespace GlobalTheory.SpanIdem

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

variable {Γ X A : Type} [Group Γ] [CommRing A] {n r t : ℕ}

theorem overK_apply {k : ℕ} (σ : Γ →* GL (Fin k) A) (g : Γ) (u : Fin k → FractionRing A) :
    overK σ g u = ((mat σ g).map (toFr A)).mulVec u := rfl

theorem map_smul_mulVec {k : ℕ} (c : A) (M : Matrix (Fin k) (Fin k) A) (u : Fin k → FractionRing A) :
    ((c • M).map (toFr A)).mulVec u = toFr A c • (M.map (toFr A)).mulVec u := by
  rw [← Matrix.smul_mulVec]
  congr 1
  ext i j
  simp

theorem map_sum_mulVec {k m : ℕ} (M : Fin m → Matrix (Fin k) (Fin k) A) (u : Fin k → FractionRing A) :
    ((∑ i, M i).map (toFr A)).mulVec u = ∑ i, ((M i).map (toFr A)).mulVec u := by
  rw [← Matrix.sum_mulVec]
  congr 1
  exact map_sum (toFr A).mapMatrix M Finset.univ

theorem map_mul_mulVec {k : ℕ} (M N : Matrix (Fin k) (Fin k) A) (u : Fin k → FractionRing A) :
    ((M * N).map (toFr A)).mulVec u = (M.map (toFr A)).mulVec ((N.map (toFr A)).mulVec u) := by
  rw [Matrix.map_mul, Matrix.mulVec_mulVec]

theorem map_one_sub_mulVec {k : ℕ} (M : Matrix (Fin k) (Fin k) A) (u : Fin k → FractionRing A) :
    ((1 - M).map (toFr A)).mulVec u = u - (M.map (toFr A)).mulVec u := by
  have : (1 - M).map (toFr A) = 1 - M.map (toFr A) := by
    have h := map_sub (toFr A).mapMatrix 1 M
    rw [map_one] at h
    exact h
  rw [this, Matrix.sub_mulVec, Matrix.one_mulVec]

theorem eq_of_mulVec {k : ℕ} {M N : Matrix (Fin k) (Fin k) A}
    (h : ∀ u, (M.map (toFr A)).mulVec u = (N.map (toFr A)).mulVec u) : M = N := by
  have h1 : M.map (toFr A) = N.map (toFr A) := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun u => ?_
    simp only [Matrix.toLin'_apply, h]
  exact Matrix.map_injective (IsFractionRing.injective A (FractionRing A)) h1

theorem exists_corner (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A)) (ρ : Γ →* GL (Fin r) A)
    (χ : ℕ → (Γ →* Aˣ)) (π : X)
    (e : (Fin n → FractionRing A) ≃ₗ[FractionRing A] ((Fin r → FractionRing A) × (Fin t → FractionRing A)))
    (hr : 2 ≤ r) (hs : Submodule.span A (Set.range (mat ρ)) = ⊤) (hd : IsDecomp (t := t) (rep π) ρ χ e)
    (P : Matrix (Fin r) (Fin r) A) :
    ∃ a, InRing T rep a ∧
      ∀ u, e (((a π).map (toFr A)).mulVec u) = ((P.map (toFr A)).mulVec (e u).1, 0) := by
  obtain ⟨m, f, h, hP, hχ⟩ := GlobalTheory.T.exists_repMatrix_combination_killing_characters ρ χ hr hs P
  refine ⟨∑ k, f k • fun x => mat (rep x) (h k),
    inRing_sum _ fun k _ => inRing_smul _ (inRing_mat _), fun u => ?_⟩
  rw [Finset.sum_apply, map_sum_mulVec, map_sum, ← hP, map_sum_mulVec]
  have key : ∀ k, e ((((f k • fun x => mat (rep x) (h k)) π).map (toFr A)).mulVec u) =
      (((f k • mat ρ (h k)).map (toFr A)).mulVec (e u).1,
        fun c : Fin t => toFr A (f k * ((χ ((c : ℕ) + 1) (h k) : Aˣ) : A)) * (e u).2 c) := by
    intro k
    rw [Pi.smul_apply, map_smul_mulVec, map_smul, ← overK_apply, hd, map_smul_mulVec, overK_apply]
    refine Prod.ext rfl ?_
    funext c
    simp [mul_assoc]
    simp [Algebra.smul_def]
  simp only [key]
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_sum]
  · rw [Prod.snd_sum]
    funext c
    rw [Finset.sum_apply]
    simp only [← Finset.sum_mul, ← map_sum, hχ, map_zero, zero_mul, Pi.zero_apply]

theorem pow_succ_eval {b : X → Matrix (Fin n) (Fin n) A} {π : X} (h : b π * b π = b π) (k : ℕ) :
    (b ^ (k + 1)) π = b π := by
  rw [Pi.pow_apply]
  exact IsIdempotentElem.pow_succ_eq k h

theorem exists_idem (l : ℕ) [Fact l.Prime] [Finite X] [Algebra ℤ_[l] A] [Module.Finite ℤ_[l] A]
    (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A)) (π : X)
    (b : X → Matrix (Fin n) (Fin n) A) (hb : InRing T rep b) (hπ : b π * b π = b π) :
    ∃ E, InRing T rep E ∧ E * E = E ∧ E π = b π ∧ (∀ y, y * b = 0 → y * E = 0) ∧
      (∀ y, b * y = 0 → E * y = 0) := by
  haveI : Module.Finite ℤ_[l] (Matrix (Fin n) (Fin n) A) :=
    inferInstanceAs (Module.Finite ℤ_[l] (Fin n → Fin n → A))
  obtain ⟨E, hE, hM⟩ := GlobalTheory.T.exists_idempotent_sub_mem_of_pow_sub_mem' l b
  refine ⟨E, ?_, hE, ?_, fun y hy => ?_, fun y hy => ?_⟩
  · have := hM ((Subalgebra.toSubmodule (ringR T rep)).restrictScalars ℤ_[l]) 0 fun k => by
      rw [sub_zero]
      exact pow_mem ((mem_ringR T rep b).2 hb) (k + 1)
    rw [sub_zero] at this
    exact (mem_ringR T rep E).1 this
  · have := hM (LinearMap.ker (LinearMap.proj π)) b fun k => by
      rw [LinearMap.mem_ker, LinearMap.proj_apply, Pi.sub_apply, pow_succ_eval hπ, sub_self]
    rw [LinearMap.mem_ker, LinearMap.proj_apply, Pi.sub_apply] at this
    exact sub_eq_zero.1 this
  · have := hM (LinearMap.ker (LinearMap.mulLeft ℤ_[l] y)) 0 fun k => by
      rw [LinearMap.mem_ker, LinearMap.mulLeft_apply, sub_zero, pow_succ', ← mul_assoc, hy, zero_mul]
    rwa [LinearMap.mem_ker, LinearMap.mulLeft_apply, sub_zero] at this
  · have := hM (LinearMap.ker (LinearMap.mulRight ℤ_[l] y)) 0 fun k => by
      rw [LinearMap.mem_ker, LinearMap.mulRight_apply, sub_zero, pow_succ, mul_assoc, hy, mul_zero]
    rwa [LinearMap.mem_ker, LinearMap.mulRight_apply, sub_zero] at this

theorem rank_single {K : Type} [Field K] (i : Fin r) :
    (Matrix.single i i (1 : K)).rank = 1 := by
  classical
  have : Matrix.single i i (1 : K) = Matrix.diagonal (Pi.single i 1) := by
    ext a b
    simp only [Matrix.single_apply, Matrix.diagonal_apply, Pi.single_apply]
    grind
  rw [this, Matrix.rank_diagonal]
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨i, by simp⟩, ?_⟩
  rintro ⟨a, ha⟩
  apply Subtype.ext
  by_contra h
  exact ha (Pi.single_eq_of_ne h 1)

theorem exists_orthogonal_idempotents : ∀ (l : ℕ) [Fact l.Prime] {Γ X A : Type} [Group Γ] [Finite X] [CommRing A] [IsDomain A] [Algebra ℤ_[l] A] [Module.Finite ℤ_[l] A] {n r t : ℕ} (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A)) (ρ : Γ →* GL (Fin r) A) (χ : ℕ → (Γ →* Aˣ)) (π : X) (e : (Fin n → FractionRing A) ≃ₗ[FractionRing A] ((Fin r → FractionRing A) × (Fin t → FractionRing A))), 2 ≤ r → Submodule.span A (Set.range (mat ρ)) = ⊤ → IsDecomp (t := t) (rep π) ρ χ e → ∃ eB e1 : X → Matrix (Fin n) (Fin n) A, (InRing T rep eB ∧ InRing T rep e1 ∧ eB * eB = eB ∧ e1 * e1 = e1 ∧ eB * e1 = 0 ∧ e1 * eB = 0) ∧ (∀ u, e (((eB π).map (toFr A)).mulVec u) = (0, (e u).2)) ∧ ∃ ε : Matrix (Fin r) (Fin r) (FractionRing A), ε.rank = 1 ∧ ∀ u, e (((e1 π).map (toFr A)).mulVec u) = (ε.mulVec (e u).1, 0) := by
  intro l _ Γ X A _ _ _ _ _ _ n r t T rep ρ χ π e hr hs hd
  obtain ⟨a, ha, hact⟩ := exists_corner T rep ρ χ π e hr hs hd 1
  have hb : ∀ u, e ((((1 - a) π).map (toFr A)).mulVec u) = (0, (e u).2) := by
    intro u
    rw [Pi.sub_apply, Pi.one_apply, map_one_sub_mulVec, map_sub, hact,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
    exact Prod.ext (by simp) (by simp)
  obtain ⟨eB, hB, hBB, hBπ, -, -⟩ := exists_idem l T rep π (1 - a) (inRing_sub inRing_one ha) (by
    apply eq_of_mulVec
    intro u
    apply e.injective
    rw [map_mul_mulVec, hb, hb])
  rw [← hBπ] at hb
  let i : Fin r := ⟨0, by omega⟩
  obtain ⟨a', ha', hact'⟩ := exists_corner T rep ρ χ π e hr hs hd (Matrix.single i i 1)
  have hε : (Matrix.single i i (1 : A)).map (toFr A) = Matrix.single i i 1 := by
    rw [Matrix.map_single, map_one]
  rw [hε] at hact'
  have hc : ∀ u, e ((((1 - eB) π).map (toFr A)).mulVec u) = ((e u).1, 0) := by
    intro u
    rw [Pi.sub_apply, Pi.one_apply, map_one_sub_mulVec, map_sub, hb]
    exact Prod.ext (by simp) (by simp)
  have hb' : ∀ u, e (((((1 - eB) * a' * (1 - eB)) π).map (toFr A)).mulVec u) =
      ((Matrix.single i i 1).mulVec (e u).1, 0) := by
    intro u
    rw [Pi.mul_apply, Pi.mul_apply, map_mul_mulVec, map_mul_mulVec, hc, hact', hc]
  have h1 := inRing_sub inRing_one hB
  obtain ⟨e1, h1R, h11, h1π, hl, hrr⟩ := exists_idem l T rep π ((1 - eB) * a' * (1 - eB))
    (inRing_mul (inRing_mul h1 ha') h1) (by
      apply eq_of_mulVec
      intro u
      apply e.injective
      rw [map_mul_mulVec, hb', hb', Matrix.mulVec_mulVec, Matrix.single_mul_single_same, one_mul])
  refine ⟨eB, e1, ⟨hB, h1R, hBB, h11, hl eB ?_, hrr eB ?_⟩, hb, Matrix.single i i 1, rank_single i, ?_⟩
  · rw [← mul_assoc, ← mul_assoc, mul_sub eB 1 eB, mul_one, hBB, sub_self, zero_mul, zero_mul]
  · rw [mul_assoc, sub_mul 1 eB eB, one_mul, hBB, sub_self, mul_zero]
  · rw [h1π]
    exact hb'

end GlobalTheory.SpanIdem

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowSmulMem
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory.IntegralPowerScalar

theorem exists_pow_mul_integral {l : ℕ} [Fact (Nat.Prime l)] (LL : FinExt l) (c : ↥LL.1) :
    ∃ n : ℕ, (l : ↥LL.1) ^ n * c ∈ OL LL := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have h1 : IsAlgebraic ℚ_[l] c := IsAlgebraic.of_finite ℚ_[l] c
  have h2 : IsAlgebraic ℤ_[l] c := (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥LL.1).2 h1
  obtain ⟨y, hy, hint⟩ := h2.exists_integral_multiple
  refine ⟨y.valuation, ?_⟩
  have hs := PadicInt.unitCoeff_spec hy
  have hm : y • c ∈ OL LL := hint
  have hm2 := (OL LL).smul_mem hm (((PadicInt.unitCoeff hy)⁻¹ : ℤ_[l]ˣ) : ℤ_[l])
  have he : (((PadicInt.unitCoeff hy)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) * y = (l : ℤ_[l]) ^ y.valuation := by
    exact (Units.inv_mul_eq_iff_eq_mul _).2 hs
  rw [smul_smul, he, Algebra.smul_def, map_pow, map_natCast] at hm2
  exact hm2

theorem smul_mem_of_mem {l : ℕ} [Fact (Nat.Prime l)] {LL : FinExt l} (T : GlobalTheory.BKGal.QLat LL)
    {c : ↥LL.1} (hc : c ∈ OL LL) {x : T.V} (hx : x ∈ T.L.T) : c • x ∈ T.L.T := by
  have h := T.L.T.smul_mem (⟨c, hc⟩ : ↥(OL LL)) hx
  rw [← algebraMap_smul ↥LL.1 (⟨c, hc⟩ : ↥(OL LL)) x] at h
  exact h

theorem exists_pow_smul_mem {l : ℕ} [inst : Fact (Nat.Prime l)] {LL : FinExt l}
    (T : GlobalTheory.BKGal.QLat LL) (v : T.V) : ∃ n : ℕ, (l : ↥LL.1) ^ n • v ∈ T.L.T := by
  have hl : ∀ k : ℕ, (l : ↥LL.1) ^ k ∈ OL LL := fun k => pow_mem (natCast_mem (OL LL) l) k
  have hv : v ∈ Submodule.span ↥LL.1 (T.L.T : Set T.V) := by
    rw [T.L.span]; exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨0, by rw [pow_zero, one_smul]; exact hx⟩
  | zero => exact ⟨0, by rw [smul_zero]; exact T.L.T.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := hy
    refine ⟨m + n, ?_⟩
    have h1 := smul_mem_of_mem T (hl n) hm
    have h2 := smul_mem_of_mem T (hl m) hn
    rw [smul_smul, ← pow_add, Nat.add_comm] at h1
    rw [smul_smul, ← pow_add] at h2
    rw [smul_add]
    exact T.L.T.add_mem h1 h2
  | smul c x _ hx =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := exists_pow_mul_integral LL c
    refine ⟨n + m, ?_⟩
    have h := smul_mem_of_mem T hn hm
    have e : (l : ↥LL.1) ^ (n + m) * c = (l : ↥LL.1) ^ n * c * (l : ↥LL.1) ^ m := by ring
    have e2 : (l : ↥LL.1) ^ (n + m) • c • x = ((l : ↥LL.1) ^ n * c) • (l : ↥LL.1) ^ m • x :=
      (smul_smul _ _ x).trans ((congrArg (fun a : ↥LL.1 => a • x) e).trans (smul_smul _ _ x).symm)
    exact Eq.mpr (congrArg (fun w : T.V => w ∈ T.L.T) e2) h

end GlobalTheory.IntegralPowerScalar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowSmulMemLattice
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.LatticePowerScalar

theorem exists_pow_mul_isIntegral {l : ℕ} [Fact l.Prime] {K : Type} [Field K] [Algebra ℚ_[l] K]
    [Algebra ℤ_[l] K] [IsScalarTower ℤ_[l] ℚ_[l] K] {c : K} (hc : IsAlgebraic ℚ_[l] c) :
    ∃ n : ℕ, IsIntegral ℤ_[l] ((l : K) ^ n * c) := by
  have h1 : IsAlgebraic ℤ_[l] c := (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] K).2 hc
  obtain ⟨y, hy, hyc⟩ := h1.exists_integral_multiple
  refine ⟨y.valuation, ?_⟩
  have h2 : (((PadicInt.unitCoeff hy)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) * y = (l : ℤ_[l]) ^ y.valuation := by
    rw [Units.inv_mul_eq_iff_eq_mul]
    exact PadicInt.unitCoeff_spec hy
  have h3 : (l : K) ^ y.valuation * c = (((PadicInt.unitCoeff hy)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) • (y • c) := by
    rw [← mul_smul, h2, Algebra.smul_def, map_pow, map_natCast]
  rw [h3]
  exact hyc.smul _

theorem exists_pow_smul_mem {O K V : Type} [CommRing O] [CommRing K] [Algebra O K] [AddCommGroup V]
    [Module K V] [Module O V] [IsScalarTower O K V] (p : O)
    (hp : ∀ c : K, ∃ (n : ℕ) (o : O), algebraMap O K p ^ n * c = algebraMap O K o)
    (M : Submodule O V) (v : V) (hv : v ∈ Submodule.span K (M : Set V)) :
    ∃ n : ℕ, algebraMap O K p ^ n • v ∈ M := by
  have up : ∀ (n k : ℕ) (x : V), algebraMap O K p ^ n • x ∈ M → algebraMap O K p ^ (k + n) • x ∈ M := by
    intro n k x hx
    rw [pow_add, mul_smul, ← map_pow, algebraMap_smul]
    exact M.smul_mem _ hx
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨0, by rwa [pow_zero, one_smul]⟩
  | zero => exact ⟨0, by rw [smul_zero]; exact M.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := hy
    refine ⟨m + n, ?_⟩
    rw [smul_add]
    exact M.add_mem (add_comm n m ▸ up m n x hm) (up n m y hn)
  | smul c x _ hx =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, o, ho⟩ := hp c
    refine ⟨n + m, ?_⟩
    have h : algebraMap O K p ^ (n + m) • c • x = o • (algebraMap O K p ^ m • x) := by
      rw [← algebraMap_smul K o, ← ho, smul_smul, smul_smul, pow_add]
      congr 1
      ring
    rw [h]
    exact M.smul_mem _ hm

theorem exists_pow_smul_mem_lattice {l : ℕ} [Fact (Nat.Prime l)] (LL : FinExt l) (T : GlobalTheory.BKGal.QLat LL) :
    ∀ v ∈ Submodule.span ↥LL.1 ((T.L.T : Submodule ↥(OL LL) T.V) : Set T.V),
      ∃ n : ℕ, (l : ↥LL.1) ^ n • v ∈ T.L.T := by
  intro v hv
  have hl : algebraMap ↥(OL LL) ↥LL.1 (l : ↥(OL LL)) = (l : ↥LL.1) := map_natCast _ l
  rw [← hl]
  refine exists_pow_smul_mem (l : ↥(OL LL)) (fun c => ?_) T.L.T v hv
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  obtain ⟨n, hn⟩ := exists_pow_mul_isIntegral (l := l) (Algebra.IsAlgebraic.isAlgebraic (R := ℚ_[l]) c)
  exact ⟨n, ⟨(l : ↥LL.1) ^ n * c, hn⟩, by rw [hl]; rfl⟩

end GlobalTheory.LatticePowerScalar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowFixingNormalOfNear
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.PowFixNear
open GlobalTheory.MemLoc GlobalTheory.MemLoc.FrobLaws

theorem main : ∀ (l : ℕ) [Fact l.Prime] (F : FinExt l), Normal ℚ_[l] ↥F.1 → ∀ g : GQ l, (∀ x ∈ F.1, x ≠ 0 → ‖g x - x‖ < ‖x‖) → ∃ s : ℕ, ∀ x ∈ F.1, (g ^ l ^ s) x = x := by
  intro l _ F hF g hg
  haveI := F.2
  haveI : Normal ℚ_[l] ↥F.1 := hF
  have hpow : ∀ (i : ℕ) (x : Om l), x ∈ F.1 → x ≠ 0 → ‖(g ^ i) x - x‖ < ‖x‖ := by
    intro i x hx hx0
    induction i with
    | zero => simpa using hx0
    | succ i ih =>
      have e : (g ^ (i + 1)) x - x = (g ^ i) (g x - x) + ((g ^ i) x - x) := by
        rw [pow_succ, AlgEquiv.mul_apply, map_sub (g ^ i)]; ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ih)
      rw [norm_gal]; exact hg x hx hx0
  have hst : ∀ (h : GQ l) (x : Om l), x ∈ F.1 → h x ∈ F.1 := by
    intro h x hx
    have e := AlgEquiv.restrictNormal_commutes h (↥F.1) ⟨x, hx⟩
    have e' : h x = (algebraMap (↥F.1) (Om l)) ((AlgEquiv.restrictNormal h (↥F.1)) ⟨x, hx⟩) := e.symm
    rw [e']
    exact ((AlgEquiv.restrictNormal h (↥F.1)) ⟨x, hx⟩).2
  set r := AlgEquiv.restrictNormalHom (F := ℚ_[l]) (K₁ := Om l) (↥F.1) with hr
  have hfin : IsOfFinOrder (r g) := isOfFinOrder_of_finite _
  set N := orderOf (r g) with hNdef
  have hN0 : N ≠ 0 := (hfin.orderOf_pos).ne'
  have hgN : ∀ x ∈ F.1, (g ^ N) x = x := by
    intro x hx
    have e := AlgEquiv.restrictNormal_commutes (g ^ N) (↥F.1) ⟨x, hx⟩
    have h1 : AlgEquiv.restrictNormal (g ^ N) (↥F.1) = 1 := by
      have := pow_orderOf_eq_one (r g)
      rw [← map_pow] at this
      exact this
    rw [h1] at e
    simpa using e.symm
  obtain ⟨s, N', hN', hNe⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN0 l (Fact.out : l.Prime).ne_one
  refine ⟨s, fun y hy => ?_⟩
  refine GlobalTheory.TameInertiaCyclic.fix_of_near F (g ^ l ^ s) (hst _) (fun x hx hx0 => hpow _ x hx hx0) hN' (fun x hx => ?_) y hy
  rw [← pow_mul, ← hNe]
  exact hgN x hx

end GlobalTheory.PowFixNear
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteLevelCupSwapCoboundaryIffStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_level_cup_swap_coboundary_iff : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ (ϖ : O) (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), ∀ s ∈ quotientCocycles LA _ hI, ∀ d : ↥(latticeCocycles LA'), CobO (P.PD K) L1 (GlobalTheory.BKFinLevel.cupQ LA LA' m ϖ r s (redT LA' _ d)) ↔ CobO (P.PD K) L1 (cupLD LA m.flip (d : ↥(GK K) → A'.V) (fun g => GlobalTheory.BKFinLevel.ioL LA ϖ r (s g))) := by
  first | exact @GlobalTheory.BKSwapCup.cobO_cupQ_iff | exact GlobalTheory.BKSwapCup.cobO_cupQ_iff | (intros; apply GlobalTheory.BKSwapCup.cobO_cupQ_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HostFieldImageMemUnramifiedAdjoinRootsOfUnityStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hostField_image_mem_unramified_adjoin_rootsOfUnity : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (x : D.host.E), (D.nbr i w hw).j (algebraMap D.host.E D.nd.Om x) ∈ MaximalUnramifiedExtension (D.nd.l i) ⊔ IntermediateField.adjoin ℚ_[D.nd.l i] {y : Om (D.nd.l i) | y ^ (D.nd.l i ^ D.nd.s0 i) = 1} := by
  first | exact @GlobalTheory.HostImage.host_image_mem | exact GlobalTheory.HostImage.host_image_mem | (intros; apply GlobalTheory.HostImage.host_image_mem <;> assumption)
end

