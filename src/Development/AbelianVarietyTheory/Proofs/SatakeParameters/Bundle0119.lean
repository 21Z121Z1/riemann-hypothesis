import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationLeOneOfMemZmu
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastTwoStepsGuarded
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0114
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0087
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0079
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0075
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0054

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotDvdCardStabFrm
section
noncomputable section

namespace GlobalTheory.ColPeriod

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke.FourierColumnIndicator (FnModAt FnMod facTop facPen Zmu)
open GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance (DegOneUnram)
open GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation (StdOver IsFrames)
open GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable (jetSum RatIdx)
open GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint (WtCompat InDeg HAt LatWithBasis)

section Generic

variable {K : Type} [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K))

def Bd {V V' : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V']
    (c : K) (M : Submodule (𝓞 K) V) (M' : Submodule (𝓞 K) V') (k : V →ₗ[K] V') : Prop :=
  ∀ v ∈ localization₂ w.asIdeal M, c • k v ∈ localization₂ w.asIdeal M'

def WtUnit (S : GSD K) : Prop := ∀ d : S.D, w.valuation K ((Nat.card (MulAction.stabilizer S.G d) : ℕ) : K)⁻¹ ≤ 1

variable {w}

theorem Bd.transfer {S S' : GSD K} (g : S.G) (g' : S'.G) {M M₂ : Submodule (𝓞 K) S.V} {M' M₂' : Submodule (𝓞 K) S'.V}
    (hM : M₂ = M.map ((S.ρ g).restrictScalars (𝓞 K))) (hM' : M₂' = M'.map ((S'.ρ g').restrictScalars (𝓞 K)))
    {k k₂ : S.V →ₗ[K] S'.V} (hk : k₂ = (S'.ρ g') ∘ₗ k ∘ₗ (S.ρ g⁻¹)) {c : K} (h : Bd w c M₂ M₂' k₂) : Bd w c M M' k := by
  subst hM hM' hk
  rintro v ⟨s, hs, hv⟩
  obtain ⟨t, ht, y, hy, e⟩ := h (S.ρ g v) ⟨s, hs, s • v, hv, by simp⟩
  refine ⟨t, ht, ?_⟩
  have e1 : S.ρ g⁻¹ (S.ρ g v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have e2 : y = t • c • k v := by
    have h2 := congrArg (S'.ρ g'⁻¹) e
    simp only [LinearMap.restrictScalars_apply, LinearMap.comp_apply, e1, LinearMap.map_smul_of_tower, map_smul] at h2
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one] at h2
    exact h2
  exact e2 ▸ hy

theorem opOf_bound {S S' : GSD K} (A : ClsKer S S') (h : S.Ok) (s : S.Sec) (hw : WtUnit w S) {c : K}
    (hk : ∀ d d', Bd w c (S.Del d) (S'.Del d') (A.k d d')) {c₀ : K} (φ : S.EqFun)
    (hφ : ∀ d, c₀ • φ.1 d ∈ localization₂ w.asIdeal (S.Del d)) (d' : S'.D) :
    (c * c₀) • (A.opOf h s φ).1 d' ∈ localization₂ w.asIdeal (S'.Del d') := by
  change (c * c₀) • A.appOf h s φ d' ∈ _
  unfold ClsKer.appOf
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun x _ => ?_
  rw [smul_comm, wt_eq_card]
  refine smul_mem_localizationAt_of_le w _ (hw _) ?_
  rw [mul_smul, ← map_smul]
  exact hk _ _ _ (hφ _)

theorem comp_bound {S₀ S S₁ : GSD K} {Y : Cpl S} (A : CplKer S₀ S S₁ Y) (h : S.Ok) (s : S.Sec) (hw : WtUnit w S) {c₁ c₂ : K}
    (h1 : ∀ d₀ d, ∀ y ∈ Y.ys d, Bd w c₁ (S₀.Del d₀) (S.Del d) (A.k1 d₀ d y))
    (h2 : ∀ d d₁, ∀ y ∈ Y.ys d, Bd w c₂ (S.Del d) (S₁.Del d₁) (A.k2 d y d₁)) (d₀ : S₀.D) (d₁ : S₁.D) :
    Bd w (c₂ * c₁) (S₀.Del d₀) (S₁.Del d₁) ((A.comp h s).k d₀ d₁) := by
  intro v hv
  simp only [CplKer.comp, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun x _ => ?_
  rw [smul_comm, wt_eq_card]
  refine smul_mem_localizationAt_of_le w _ (hw _) ?_
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun y hy => ?_
  have hy' : y ∈ Y.ys (s.rep x) := by simpa using hy
  rw [mul_smul, ← map_smul]
  exact h2 _ _ y hy' _ (h1 _ _ y hy' v hv)

theorem colTo_bound {F : ℕ → GFam K} (kk : KerFam F) (hF : ∀ j, (F j).Ok) (c : ℕ → K)
    (φ : (F 0).Forms) (hφ : ∀ b d, (φ b).1 d ∈ localization₂ w.asIdeal (((F 0).mem b).Del d)) (n : ℕ)
    (hw : ∀ j < n, ∀ b, WtUnit w ((F j).mem b))
    (hk : ∀ j < n, ∀ al be d d', Bd w (c j) (((F j).mem al).Del d) (((F (j + 1)).mem be).Del d') ((kk j al be).k d d'))
    (b : (F n).β) (d : ((F n).mem b).D) :
    (∏ j ∈ Finset.range n, c j) • (kk.colTo hF n φ b).1 d ∈ localization₂ w.asIdeal (((F n).mem b).Del d) := by
  induction n with
  | zero => rw [Finset.prod_range_zero, one_smul]; exact hφ b d
  | succ n ih =>
    have e : (kk.colTo hF (n + 1) φ b).1 d =
        ∑ al, ((kk n al b).opOf (hF n al) ((F n).mem al).outSec (kk.colTo hF n φ al)).1 d := by
      change (KerFam.step kk hF n (kk.colTo hF n φ) b).1 d = _
      simp only [KerFam.step, GFam.Mat.opOf, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.comp_apply,
        LinearMap.proj_apply, Submodule.coe_sum, Finset.sum_apply]
    rw [e, Finset.smul_sum, Finset.prod_range_succ, mul_comm]
    exact Submodule.sum_mem _ fun al _ => opOf_bound _ _ _ (hw n (Nat.lt_succ_self n) al) (hk n (Nat.lt_succ_self n) al b) _
      (ih (fun j hj => hw j (Nat.lt_succ_of_lt hj)) (fun j hj => hk j (Nat.lt_succ_of_lt hj)) al) d

theorem colCpl_bound {F : ℕ → GFam K} (kk : KerFam F) (hF : ∀ j, (F j).Ok) {n : ℕ} (hw : ∀ j ≤ n, ∀ b, WtUnit w ((F j).mem b))
    (c : ℕ → K) {S S₁ : GSD K} {Y : Cpl S} (A : ∀ b : (F n).β, CplKer ((F n).mem b) S S₁ Y) (h : S.Ok) (hS : WtUnit w S)
    (hk : ∀ j < n, ∀ al be d d', Bd w (c j) (((F j).mem al).Del d) (((F (j + 1)).mem be).Del d') ((kk j al be).k d d'))
    (h1 : ∀ b d₀ d, ∀ y ∈ Y.ys d, Bd w (c n) (((F n).mem b).Del d₀) (S.Del d) ((A b).k1 d₀ d y))
    (h2 : ∀ b d d₁, ∀ y ∈ Y.ys d, Bd w (c (n + 1)) (S.Del d) (S₁.Del d₁) ((A b).k2 d y d₁))
    (φ : (F 0).Forms) (hφ : ∀ b d, (φ b).1 d ∈ localization₂ w.asIdeal (((F 0).mem b).Del d)) (d : S₁.D) :
    (∏ j ∈ Finset.range (n + 2), c j) • (colCpl kk hF n A h φ).1 d ∈ localization₂ w.asIdeal (S₁.Del d) := by
  have e : (colCpl kk hF n A h φ).1 d =
      ∑ b, (((A b).comp h S.outSec).opOf (hF n b) ((F n).mem b).outSec (kk.colTo hF n φ b)).1 d := by
    simp only [colCpl, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, Submodule.coe_sum, Finset.sum_apply]
  have e2 : ∏ j ∈ Finset.range (n + 2), c j = (c (n + 1) * c n) * ∏ j ∈ Finset.range n, c j := by
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    ring
  rw [e, Finset.smul_sum, e2]
  exact Submodule.sum_mem _ fun b _ => opOf_bound _ _ _ (hw n le_rfl b) (comp_bound (A b) h _ hS (h1 b) (h2 b)) _
    (colTo_bound kk hF c φ hφ n (fun j hj => hw j hj.le) hk b) d

end Generic

theorem not_dvd_card_stab_frm {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}
    (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (d : DecoF X.E n ST SG Q)
    [Finite (MulAction.stabilizer (FrmG Λ Θ) d)] {p : ℕ} (hp : p.Prime) (hb : Module.finrank ℚ X.E * n + 1 < p) :
    ¬ p ∣ Nat.card (MulAction.stabilizer (FrmG Λ Θ) d) := by
  refine not_dvd_card_of_injective (((UF X.E n).subtype.comp (MonoidHom.fst _ _)).comp (Subgroup.subtype _)) ?_ hp hb
  rw [injective_iff_map_eq_one]
  rintro ⟨⟨γ, h, c⟩, hs⟩ h1
  have h2 : γ = 1 := Subtype.ext h1
  subst h2
  have h3 : h.1 = 1 := glg_eq_one_of_fix d.1.1 h.1 (congrArg (fun x : DecoF X.E n ST SG Q => x.1.1.1) hs)
  have h4 : c.1 = 1 := by
    funext P
    have h5 : (1 : Sp X.E n ≃ₗ[X.E] Sp X.E n) * d.1.2 P * ((c.1 P)⁻¹).1 = d.1.2 P :=
      congrArg (fun x : DecoF X.E n ST SG Q => x.1.2 P) hs
    rw [one_mul, mul_eq_left] at h5
    exact inv_eq_one.1 (Subtype.ext h5)
  exact Subtype.ext (Prod.ext rfl (Prod.ext (Subtype.ext h3) (Subtype.ext h4)))

theorem stdOver_tilH {E : Type} [Field E] [NumberField E] [StarRing E] {N n : ℕ} (hN : N = n + 1)
    {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {pi : 𝓞 E} (hT : ∀ P : ST, cO E pi ∉ P.1.asIdeal) (hG : ∀ v : SG, pi ∉ v.1.asIdeal)
    (d : DecoSet E n ∅ SG) {p : ℕ} (h : StdOver p d.1.N) : StdOver p (DecoSet.tilH (ST := ST) hN pi d).1.N := by
  subst hN
  change StdOver p (DecoSet.til (ST := ST) pi d).1.N
  rw [DecoSet.til_val d hT hG]
  intro P hP
  ext x
  change x ∈ localization₂ P.asIdeal (tilN d.1.N) ↔ _
  rw [mem_localization_tilN, h P hP, GlobalTheory.TopStep.mem_stdAt, GlobalTheory.TopStep.mem_stdAt, Fin.forall_fin_succ']
  rfl

section Column

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (A : Amb X)

theorem exists_std_pt (hM : StdMove) (hPr : Pr.Ok) (i : Fin 2) (u : Pr.Word) (j : ℕ) (b : L.β j)
    (p : ((chF W sel mu L u j).mem b).D) : ∃ g : ((chF W sel mu L u j).mem b).G, StdOver (Pr.g i) (DecoF.deco (g • p)).1.N := by
  obtain ⟨γ, hγ⟩ := hM X Pr hPr i _ (DecoF.deco p).1.N ⟨(DecoF.deco p).2.lat, (DecoF.deco p).2.uni⟩
  exact ⟨(γ, 1, 1), hγ⟩

theorem evGSD_del_smul (hPr : Pr.Ok) (hsel : IsSel X sel) (u : Pr.Word) (hS : Pr.T u ∈ S) (P : LevFam X.E X.K R.r Pr.vGs)
    (γ : UF X.E (R.N R.m - 1)) (d : (evGSD W Ch sel mu P u).D) :
    (evGSD W Ch sel mu P u).Del (((γ, 1) : (evGSD W Ch sel mu P u).G) • d) =
      ((evGSD W Ch sel mu P u).Del d).map (((evGSD W Ch sel mu P u).ρ (γ, 1)).restrictScalars (𝓞 X.K)) := by
  have h1 := DecoSet.tilH_smul (ST := Pr.vT u) (N_m_succ R) (γ, (1 : GLG X.E _ (rowSG Pr sel mu))) d (conj_piT_notMem hPr u)
    (piT_notMem_rowSG sel mu hPr hsel u hS)
  have h2 : (evGSD W Ch sel mu P u).ρ (γ, 1) = (colVal W u R.m (Pr.vT u) (rowSG Pr sel mu)).rho (extUH (N_m_succ R) γ) := by
    change ((((rowTy Ch sel mu P).inv.chr 1)⁻¹ : X.Kˣ) : X.K) •
      (colVal W u R.m (Pr.vT u) (rowSG Pr sel mu)).rho (extUH (N_m_succ R) γ) = _
    rw [map_one, inv_one, Units.val_one, one_smul]
  rw [h2]
  refine Eq.trans ?_ (colVal_del_smul W u R.m (extUH (N_m_succ R) γ, extGH (N_m_succ R) 1) (tilQ sel mu u d))
  exact congrArg (colVal W u R.m (Pr.vT u) (rowSG Pr sel mu)).Del h1

theorem wtUnit_chF (hX : X.Ok) (u : Pr.Word) (hF : ∀ j, (chF W sel mu L u j).Ok) {p : ℕ} (hp : p.Prime)
    (hb : 2 * X.f * R.N R.m + 1 < p) (w : HeightOneSpectrum (𝓞 X.K)) (hw : ((p : ℕ) : 𝓞 X.K) ∈ w.asIdeal) {j : ℕ} (hj : j ≤ R.m)
    (b : L.β j) : WtUnit w ((chF W sel mu L u j).mem b) := by
  intro d
  have hE : Module.finrank ℚ X.E = 2 * X.f := by
    rw [← Module.finrank_mul_finrank ℚ X.F X.E, hX.rankE, ← hX.card_Tau, mul_comm]
    rfl
  have := (hF j b).fin_stab d
  have hN : R.N j ≤ R.N R.m := Examples₂.N_mono hj
  exact (valuation_inv_natCast w hp hw (not_dvd_card_stab_frm (L.levG j b) (L.levQ j b) d hp
    (lt_of_le_of_lt (by rw [hE]; gcongr) hb))).le

end Column

end GlobalTheory.ColPeriod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceOverPInducedByAlgebraicPadicEmbedding
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H

noncomputable section

namespace GlobalTheory.DatumJets.Place

variable {K : Type} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]

theorem norm_int_le (ι : K →+* ℂ_[p]) (y : 𝓞 K) : ‖ι (y : K)‖ ≤ 1 :=
  GlobalTheory.MomPlace.norm_le_one_of_isIntegral_int (by
    convert map_isIntegral_int ι (RingOfIntegers.isIntegral_coe y)
    exact Subsingleton.elim _ _)

def smallIdeal (ι : K →+* ℂ_[p]) : Ideal (𝓞 K) where
  carrier := {y | ‖ι (y : K)‖ < 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    have : ι ((a + b : 𝓞 K) : K) = ι (a : K) + ι (b : K) := by simp
    rw [this]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have : ι ((c • a : 𝓞 K) : K) = ι (c : K) * ι (a : K) := by simp
    rw [this, norm_mul]
    have h1 := norm_int_le ι c
    nlinarith [norm_nonneg (ι (c : K)), norm_nonneg (ι (a : K))]

theorem mem_smallIdeal (ι : K →+* ℂ_[p]) (y : 𝓞 K) : y ∈ smallIdeal ι ↔ ‖ι (y : K)‖ < 1 := Iff.rfl

theorem smallIdeal_isPrime (ι : K →+* ℂ_[p]) : (smallIdeal ι).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one, mem_smallIdeal]
    simp
  · intro a b hab
    rw [mem_smallIdeal] at hab
    rw [mem_smallIdeal, mem_smallIdeal]
    have : ι ((a * b : 𝓞 K) : K) = ι (a : K) * ι (b : K) := by simp
    rw [this, norm_mul] at hab
    by_contra hcon
    push Not at hcon
    nlinarith [hcon.1, hcon.2]

theorem dvd_of_natCast_mem {R : Type*} [CommRing R] (I : Ideal R) (hI : I ≠ ⊤) {q M : ℕ} (hq : q.Prime)
    (h1 : (q : R) ∈ I) (h2 : (M : R) ∈ I) : q ∣ M := by
  by_contra hnd
  have hc : Nat.Coprime q M := (Nat.Prime.coprime_iff_not_dvd hq).2 hnd
  obtain ⟨u, v, huv⟩ : IsCoprime (q : R) (M : R) := Nat.Coprime.cast hc
  exact hI ((Ideal.eq_top_iff_one _).2
    (huv ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)))

theorem norm_p_lt_one : ‖(p : ℂ_[p])‖ < 1 := by
  have h := PadicComplex.norm_extends' p (p : ℚ_[p])
  have h2 : ‖(p : ℚ_[p])‖ < 1 := Padic.norm_p_lt_one
  rw [← h] at h2
  simpa using h2

theorem exists_embedding (w : HeightOneSpectrum (𝓞 K)) (hw : (p : 𝓞 K) ∈ w.asIdeal) :
    ∃ ι : K →+* ℂ_[p], w.asIdeal = smallIdeal ι := by
  by_contra hcon
  push Not at hcon
  have hnle : ∀ σ : K →ₐ[ℚ] ℂ_[p], ¬ w.asIdeal ≤ smallIdeal (σ : K →+* ℂ_[p]) := by
    intro σ hle
    exact hcon (σ : K →+* ℂ_[p]) (w.isMaximal.eq_of_le (smallIdeal_isPrime _).ne_top hle)
  have σ0 : K →ₐ[ℚ] ℂ_[p] := IsAlgClosed.lift
  have hav : ¬ ((w.asIdeal : Set (𝓞 K)) ⊆
      ⋃ σ ∈ ((Finset.univ : Finset (K →ₐ[ℚ] ℂ_[p])) : Set (K →ₐ[ℚ] ℂ_[p])),
        (smallIdeal (σ : K →+* ℂ_[p]) : Set (𝓞 K))) := by
    rw [Ideal.subset_union_prime σ0 σ0 (fun σ _ _ _ => smallIdeal_isPrime _)]
    rintro ⟨σ, -, hle⟩
    exact hnle σ hle
  obtain ⟨x, hxw, hx⟩ := Set.not_subset.1 hav
  have hxσ : ∀ σ : K →ₐ[ℚ] ℂ_[p], 1 ≤ ‖σ (x : K)‖ := by
    intro σ
    by_contra hlt
    exact hx (Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_univ σ)) (not_le.1 hlt))
  have hN : ((Algebra.norm ℤ x).natAbs : 𝓞 K) ∈ w.asIdeal := by
    have h1 := Ideal.absNorm_mem (Ideal.span {x})
    rw [Ideal.absNorm_span_singleton] at h1
    exact (Ideal.span_singleton_le_iff_mem _).2 hxw h1
  have hpN : p ∣ (Algebra.norm ℤ x).natAbs :=
    dvd_of_natCast_mem w.asIdeal w.isPrime.ne_top Fact.out hw hN
  obtain ⟨m, hm⟩ : (p : ℤ) ∣ Algebra.norm ℤ x := Int.natCast_dvd.2 hpN
  have hprod : ((Algebra.norm ℤ x : ℤ) : ℂ_[p]) = ∏ σ : K →ₐ[ℚ] ℂ_[p], σ (x : K) := by
    rw [← Algebra.norm_eq_prod_embeddings ℚ ℂ_[p] (x : K), ← Algebra.coe_norm_int x]
    simp
  have h1 : 1 ≤ ‖((Algebra.norm ℤ x : ℤ) : ℂ_[p])‖ := by
    rw [hprod, norm_prod]
    exact Finset.prod_induction _ (fun t : ℝ => 1 ≤ t) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb)
      le_rfl fun σ _ => hxσ σ
  have h2 : ((Algebra.norm ℤ x : ℤ) : ℂ_[p]) = (p : ℂ_[p]) * ((m : ℤ) : ℂ_[p]) := by
    rw [hm]; push_cast; ring
  have h3 : ‖((m : ℤ) : ℂ_[p])‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one _ m
  rw [h2, norm_mul] at h1
  have h4 := norm_p_lt_one (p := p)
  nlinarith [norm_nonneg (p : ℂ_[p]), norm_nonneg ((m : ℤ) : ℂ_[p])]

theorem valuation_le_one_of_norm (ι : K →+* ℂ_[p]) (w : HeightOneSpectrum (𝓞 K))
    (hw : ∀ y : 𝓞 K, y ∈ w.asIdeal ↔ ‖ι (y : K)‖ < 1) (x : K) (hx : ‖ι x‖ ≤ 1) :
    w.valuation K x ≤ 1 := by
  by_contra hcon
  have hgt : 1 < w.valuation K x := not_le.1 hcon
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hgt
  have hinv : w.valuation K x⁻¹ < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ hgt
  obtain ⟨n, d, h⟩ := w.exists_primeCompl_mul_eq_of_integer x⁻¹ hinv.le
  have hd : 1 ≤ ‖ι ((d : 𝓞 K) : K)‖ := not_lt.1 fun hlt => d.2 ((hw _).2 hlt)
  have hn : n ∈ w.asIdeal := by
    rw [← w.valuation_lt_one_iff_mem (K := K)]
    change w.valuation K (algebraMap (𝓞 K) K n) < 1
    rw [← h, map_mul]
    calc w.valuation K x⁻¹ * w.valuation K (algebraMap (𝓞 K) K d) ≤ w.valuation K x⁻¹ * 1 :=
          mul_le_mul_right (w.valuation_le_one _) _
      _ < 1 := by rwa [mul_one]
  have hn' := (hw n).1 hn
  have h2 : ((d : 𝓞 K) : K) = x * (n : K) := by
    have h' : x⁻¹ * ((d : 𝓞 K) : K) = (n : K) := h
    rw [← h', ← mul_assoc, mul_inv_cancel₀ hx0, one_mul]
  rw [h2, map_mul, norm_mul] at hd
  nlinarith [norm_nonneg (ι x), norm_nonneg (ι (n : K))]

theorem placeAbove : GlobalTheory.DatumJets.PlaceAbove := by
  intro K _ _ σ p _ w hw
  obtain ⟨ι, hι⟩ := exists_embedding w hw
  have hw' : ∀ y : 𝓞 K, y ∈ w.asIdeal ↔ ‖ι (y : K)‖ < 1 := fun y => by rw [hι]; rfl
  obtain ⟨lam, hlam⟩ := GlobalTheory.MomPlace.exists_extension K p σ ι
  refine ⟨lam, fun k => ?_⟩
  unfold GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions.IntAt
  rw [(hlam k).2]
  exact ⟨fun h => valuation_le_one_of_norm ι w hw' k h.2,
    fun h => ⟨(hlam k).1, GlobalTheory.MomPlace.norm_le_one_of_valuation K p ι w hw' k h⟩⟩

end GlobalTheory.DatumJets.Place
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ReprMemOfBasisRational
section
open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HeckeRational

open Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Bridge Formalism.L2.Theta
open scoped TensorProduct

theorem repr_mem_of_basis_rational {K V ι κ : Type} [Field K] [AddCommGroup V] [Module K V] [Fintype ι] [Fintype κ]
    (F : Subfield K) (b : Module.Basis ι K V) (b' : Module.Basis κ K V) (h : ∀ i j, b'.repr (b i) j ∈ F)
    (v : V) (hv : ∀ j, b'.repr v j ∈ F) (i : ι) : b.repr v i ∈ F := by
  obtain ⟨φ, h1, h2⟩ := FormsDescent.exists_retraction F
  have e2 : FormsDescent.coordMap F b' φ v = v := by
    apply b'.repr.injective
    ext j
    rw [FormsDescent.repr_coordMap, h2 _ (hv j)]
  have key : v = ∑ a, φ (b.repr v a) • b a := by
    rw [← FormsDescent.coordMap_sum F b' φ _ _ h, b.sum_repr, e2]
  have : b.repr v i = φ (b.repr v i) := by
    conv_lhs => rw [key]
    rw [b.repr_sum_self]
  rw [this]
  exact h1 _

theorem repr_map_mem {K V κ : Type} [Field K] [AddCommGroup V] [Module K V] [Fintype κ]
    (F : Subfield K) (b : Module.Basis κ K V) (g : V →ₗ[K] V) (hg : ∀ i j, b.repr (g (b j)) i ∈ F)
    (v : V) (hv : ∀ j, b.repr v j ∈ F) (i : κ) : b.repr (g v) i ∈ F := by
  have h1 : g v = ∑ j, b.repr v j • g (b j) := by
    conv_lhs => rw [← b.sum_repr v]
    simp only [map_sum, map_smul]
  rw [h1]
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  exact F.sum_mem fun j _ => F.mul_mem (hv j) (hg i j)

theorem levFn_isOfFinOrder {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (L : Formalism.L2.DIV.LevDat E ℂ n) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    IsOfFinOrder (levFn β L x) := by
  have hfin : ∀ PP : Pl E, Finite (kP PP) := fun PP => Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot
  have hone : IsOfFinOrder (1 : ℂˣ) := IsOfFinOrder.one
  unfold levFn
  refine IsOfFinOrder.mul (IsOfFinOrder.mul ?_ ?_) ?_
  · unfold ext1
    split_ifs
    · exact MonoidHom.isOfFinOrder _ (isOfFinOrder_of_finite _)
    · exact hone
  · refine Finset.prod_induction _ IsOfFinOrder (fun _ _ => IsOfFinOrder.mul) hone fun PP _ => ?_
    refine Finset.prod_induction _ IsOfFinOrder (fun _ _ => IsOfFinOrder.mul) hone fun c _ => ?_
    exact MonoidHom.isOfFinOrder _ (isOfFinOrder_of_finite _)
  · refine Finset.prod_induction _ IsOfFinOrder (fun _ _ => IsOfFinOrder.mul) hone fun PP _ => ?_
    exact MonoidHom.isOfFinOrder _ (isOfFinOrder_of_finite _)

variable {D : D7}

theorem levEnv_chi_pow (V : TH.HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    (k : (levEnv V β L).J) : ∃ n : ℕ, 0 < n ∧ (levEnv V β L).χ k ^ n = 1 :=
  isOfFinOrder_iff_pow_eq_one.1 (levFn_isOfFinOrder β (Lev.flag1L L) _)

theorem embE_mem_cmMax (x : D.host.E) : D.embE x ∈ cmMax D.what₂.LL := by
  intro σ
  rw [← D.embE_conj]
  exact D.host.conjE_apply (σ.comp D.embE) x

theorem labLL_mem_cmMax (τ : D.what₂.Tau) (x : D.host.E) : labLL D τ x ∈ cmMax D.what₂.LL := embE_mem_cmMax _

theorem action_rational (V : TH.HSp D) (C : CoefDat D V) {S : CSD D.what₂.LL} {J : Subgroup (Gf V)} {χ : J →* ℂˣ}
    (P : ClassPres (ratF V) S D.what₂.embLL C.ρ J χ) {lam : D.what₂.Tau → DomWeight V.rank}
    {c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] C.W} {pair nab del}
    {rho : GL (Fin V.rank) D.host.E →* Module.End D.what₂.LL (VV D.what₂.LL lam)}
    (hP : CoefTie V C P lam c0 pair nab del) (hM : CoefMapTie V C c0 rho)
    (hrho : ∀ g i j, (bVV D.what₂.LL lam).repr (rho g (bVV D.what₂.LL lam j)) i ∈ cmMax D.what₂.LL) (γ : GQ V) (j : S.ιV) :
    ∃ c : S.ιV → D.what₂.LL, (∀ i, c i ∈ cmMax D.what₂.LL) ∧
      C.ρ γ (P.coef (S.bV j)) = ∑ i, D.what₂.embLL (c i) • P.coef (S.bV i) := by
  obtain ⟨e, hr, he, -⟩ := hP
  obtain ⟨γE, hγ⟩ : ∃ γE, IsRatMat V γ γE := by
    obtain ⟨g, hg⟩ := γ.2
    exact ⟨g, hg.2.symm⟩
  refine ⟨fun i => (S.bV.map e).repr (rho γE (e (S.bV j))) i, fun i => ?_, ?_⟩
  · exact repr_mem_of_basis_rational _ (S.bV.map e) (bVV D.what₂.LL lam) hr _
      (repr_map_mem _ _ _ (hrho γE) _ (hr j)) i
  · rw [he, ← hM.1 γ γE hγ]
    conv_lhs => rw [← (S.bV.map e).sum_repr (rho γE (e (S.bV j)))]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [he, LinearMap.map_smulₛₗ, Module.Basis.map_apply]

theorem dcOp_matrix_mem_cmMax (V : TH.HSp D) (C : CoefDat D V) (β : GL (Fin V.rank) (Lev.EAf D))
    (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) {S : CSD D.what₂.LL}
    (P : ClassPres (ratF V) S D.what₂.embLL C.ρ (levEnv V β L).J (levEnv V β L).χ) {lam : D.what₂.Tau → DomWeight V.rank}
    {c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] C.W} {pair nab del}
    {rho : GL (Fin V.rank) D.host.E →* Module.End D.what₂.LL (VV D.what₂.LL lam)}
    (hP : CoefTie V C P lam c0 pair nab del) (hM : CoefMapTie V C c0 rho)
    (hrho : ∀ g i j, (bVV D.what₂.LL lam).repr (rho g (bVV D.what₂.LL lam j)) i ∈ cmMax D.what₂.LL)
    (B : Finset (Gf V)) (T : Module.End D.what₂.LL S.Forms)
    (hT : ∀ f : S.Forms, P.ext ((T f : S.Forms) : S.Cl → S.V) = dcOp B (P.ext (f : S.Cl → S.V))) :
    S.HasRatBasis ∧ ∀ a b, LinearMap.toMatrix S.basis S.basis T a b ∈ cmMax D.what₂.LL :=
  GlobalTheory.classPres_dcOp_rat (ratF V) S D.what₂.embLL C.ρ _ _ P B T D.starLL_cx (levEnv_chi_pow V β L)
    (action_rational V C P hP hM hrho) hT

theorem toMatrix_one_mem {K M ι : Type} [Field K] [AddCommGroup M] [Module K M] [Fintype ι] [DecidableEq ι] (F : Subfield K)
    (b : Module.Basis ι K M) (i j : ι) : LinearMap.toMatrix b b (1 : Module.End K M) i j ∈ F := by
  rw [LinearMap.toMatrix_one, Matrix.one_apply]
  split_ifs
  · exact F.one_mem
  · exact F.zero_mem

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem rows_dcOp_mem_cmMax (R : RealDat D A Ks) (h : R.fam_tie) (t : T) (B : Finset (Gf D.sp.X'))
    (U : Module.End D.what₂.LL (A.MtildeCSD t).Forms)
    (hU : ∀ f : (A.MtildeCSD t).Forms, (R.B.R t).pres.ext (U f).1 = dcOp B ((R.B.R t).pres.ext f.1)) (a b) :
    LinearMap.toMatrix (A.MtildeCSD t).basis (A.MtildeCSD t).basis U a b ∈ cmMax D.what₂.LL := by
  obtain ⟨gramR, c0R, c0L, hT⟩ := h
  exact (dcOp_matrix_mem_cmMax D.sp.X' R.cX.coef R.βX (R.datXt t) (R.B.R t).pres (hT.coefR t) hT.mapR
    (fun g i j => (coefAction_repr_mem_subfield (labLL D) _ _ labLL_mem_cmMax g i j).1) B U hU).2 a b

theorem lifts_dcOp_mem_cmMax (R : RealDat D A Ks) (h : R.fam_tie) (j : Fin D.R.m) (t : T) (B : Finset (Gf (Vc D j)))
    (U : Module.End D.what₂.LL (A.MtCSD j t).Forms)
    (hU : ∀ f : (A.MtCSD j t).Forms, (R.B.L j t).pres.ext (U f).1 = dcOp B ((R.B.L j t).pres.ext f.1)) (a b) :
    LinearMap.toMatrix (A.MtCSD j t).basis (A.MtCSD j t).basis U a b ∈ cmMax D.what₂.LL := by
  obtain ⟨gramR, c0R, c0L, hT⟩ := h
  exact (dcOp_matrix_mem_cmMax (Vc D j) (R.cV j).coef (R.βV j) (R.datVt j t) (R.B.L j t).pres (hT.coefL j t) (hT.mapL j)
    (fun g i k => (coefAction_repr_mem_subfield (labLL D) _ _ labLL_mem_cmMax g i k).2) B U hU).2 a b

theorem hecke_opMat_mem_cmMax : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.Char F → (∀ t i a b, (A.fam.R t).opMat i a b ∈ Formalism.DivisionValues.cmMax D.what₂.LL) ∧ ∀ j t i a b, (A.fam.L j t).opMat i a b ∈ Formalism.DivisionValues.cmMax D.what₂.LL := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC
  refine ⟨fun t i a b => ?_, fun j t i a b => ?_⟩
  · obtain ⟨P, k⟩ := i
    show LinearMap.toMatrix (A.MtildeCSD t).basis (A.MtildeCSD t).basis (A.heckeR t (P, k)) a b ∈ _
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [(hC.fam.degR t P).1]
      exact toMatrix_one_mem _ _ _ _
    rcases le_or_gt k D.sp.X'.rank with hk' | hk'
    · exact rows_dcOp_mem_cmMax R hC.fam.tie t _ _ ((R.B.R t).hecke.op_eq (P, k) ⟨hk, hk'⟩) a b
    · rw [(hC.fam.degR t P).2 k hk', map_zero]
      exact Subfield.zero_mem _
  · obtain ⟨P, k⟩ := i
    show LinearMap.toMatrix (A.MtCSD j t).basis (A.MtCSD j t).basis (A.heckeL j t (P, k)) a b ∈ _
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [(hC.fam.degL j t P).1]
      exact toMatrix_one_mem _ _ _ _
    rcases le_or_gt k (Vc D j).rank with hk' | hk'
    · exact lifts_dcOp_mem_cmMax R hC.fam.tie j t _ _ ((R.B.L j t).hecke.op_eq (P, k) ⟨hk, hk'⟩) a b
    · rw [(hC.fam.degL j t P).2 k hk', map_zero]
      exact Subfield.zero_mem _

end GlobalTheory.HeckeRational

end
end

