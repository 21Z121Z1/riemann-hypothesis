import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0011
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0022
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0116
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DualIsConjOfIsCsd
section
noncomputable section

open NumberField IsDedekindDomain Matrix Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.LocGlobAll.Model

namespace GlobalTheory.LocGlobDual.Model

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {a : ℕ}

def phiOp (L : Type) [Field L] [NumberField L] [IsCMField L] (a : ℕ) : Module.End ℂ (Sm L a) :=
  act (.fin (PhiU a (Af L))) * act (.cpt (PhiK L a))

theorem barK_barK (k : Kinf L a) : barK (barK k) = k := Subtype.ext (by
  ext i j : 1
  exact star_star _)

theorem fin_cpt (k : GL (Fin a) (Af L)) (u : Kinf L a) :
    act (.cpt u) * act (.fin k) = act (.fin k) * act (Op.cpt u : Op L a) := by
  change rt L a _ * rt L a _ = rt L a _ * rt L a _
  rw [← map_mul, ← map_mul]
  exact congrArg _ (infGL_comm _ _)

theorem phiOp_mul (o : Op L a) : phiOp L a * act (invTOp (conjOp o)) = act (thetaOp o) * phiOp L a := by
  cases o with
  | fin k =>
    simp only [phiOp, conjOp, invTOp, thetaOp]
    rw [mul_assoc, fin_cpt, ← mul_assoc, ← mul_assoc]
    congr 1
    change finRep L a _ * finRep L a _ = finRep L a _ * finRep L a _
    rw [← map_mul, ← map_mul]
    congr 1
    change _ = PhiU a (Af L) * _ * (PhiU a (Af L))⁻¹ * _
    rw [inv_mul_cancel_right]
    rfl
  | cpt k =>
    simp only [phiOp, conjOp, invTOp, thetaOp, barK_barK]
    rw [← mul_assoc, fin_cpt, mul_assoc, mul_assoc]
    congr 1
    change cptRep L a _ * cptRep L a _ = cptRep L a _ * cptRep L a _
    rw [← map_mul, ← map_mul, inv_mul_cancel_right]
  | lie X =>
    simp only [phiOp, conjOp, invTOp, thetaOp]
    have h1 := GlobalTheory.CapAdInv.rt_lie (Unitary.toUnits (PhiK L a)) (-(Matrix.of X)ᴴ)
    have h2 := lie_rt_fin (E := L) (toL (-(GlobalTheory.Tw.Phi a (Cinf L) * (Matrix.of X)ᴴ * (GlobalTheory.Tw.Phi a (Cinf L))ᵀ)))
      (PhiU a (Af L))
    have e : Unitary.toUnits (PhiK L a) = PhiU a (Cinf L) := Units.ext rfl
    have e2 : (Unitary.toUnits (PhiK L a)).val * (-(Matrix.of X)ᴴ) * ((Unitary.toUnits (PhiK L a))⁻¹).val =
        -(GlobalTheory.Tw.Phi a (Cinf L) * (Matrix.of X)ᴴ * (GlobalTheory.Tw.Phi a (Cinf L))ᵀ) := by
      rw [e, mul_neg, neg_mul]; rfl
    rw [e2] at h1
    rw [mul_assoc, ← mul_assoc (act (Op.lie _))]
    exact (congrArg (act (.fin (PhiU a (Af L))) * ·) h1).trans ((mul_assoc _ _ _).symm.trans
      (congrArg (· * _) h2.symm))

theorem dualIsConj_of_isCsd {π : CuspSub L a} (h : Paired π π invTOp) (hc : π.IsCsd) : DualIsConj π := by
  obtain ⟨B, h1, h2, h3, h4, h5⟩ := h
  obtain ⟨T, hT⟩ := hc
  let P : Module.End ℂ π.V := π.op (.fin (PhiU a (Af L))) * π.op (.cpt (PhiK L a))
  let Q : Module.End ℂ π.V := π.op (.cpt (PhiK L a)⁻¹) * π.op (.fin (PhiU a (Af L))⁻¹)
  have f1 : ∀ k k' : GL (Fin a) (Af L), k * k' = 1 → ∀ φ, π.op (.fin k) (π.op (.fin k') φ) = φ := fun k k' e φ =>
    Subtype.ext (by
      change (finRep L a k * finRep L a k') φ.1 = φ.1
      rw [← map_mul, e, map_one]; rfl)
  have f2 : ∀ k k' : Kinf L a, k * k' = 1 → ∀ φ, π.op (.cpt k) (π.op (.cpt k') φ) = φ := fun k k' e φ =>
    Subtype.ext (by
      change (cptRep L a k * cptRep L a k') φ.1 = φ.1
      rw [← map_mul, e, map_one]; rfl)
  let Pe : π.V ≃ₗ[ℂ] π.V := LinearEquiv.ofLinear P Q
    (LinearMap.ext fun φ => by simp [P, Q, f1, f2]) (LinearMap.ext fun φ => by simp [P, Q, f1, f2])
  let S := Pe.trans T
  have hS : ∀ o φ, S (π.op (invTOp (conjOp o)) φ) = π.op o (S φ) := fun o φ => by
    change T _ = π.op o (T _)
    rw [← hT]
    exact congrArg T (Subtype.ext (LinearMap.congr_fun (phiOp_mul o) φ.1))
  have hS' : ∀ o φ, S.symm (π.op o φ) = π.op (invTOp (conjOp o)) (S.symm φ) := fun o φ => by
    rw [LinearEquiv.symm_apply_eq, hS, LinearEquiv.apply_symm_apply]
  refine ⟨B.flip ∘ₗ S.symm.toLinearMap, fun φ h => ?_, fun ψ h => h1 ψ fun x => ?_, fun k φ ψ => ?_, fun k φ ψ => ?_,
    fun X φ ψ => ?_⟩
  · exact (map_eq_zero_iff _ S.symm.injective).1 (h2 _ h)
  · simpa using h (S x)
  · change B _ (S.symm _) = B _ (S.symm _)
    rw [hS']; exact h3 _ _ _
  · change B _ (S.symm _) = B _ (S.symm _)
    rw [hS']; exact h4 _ _ _
  · change B _ (S.symm _) + B _ (S.symm _) = 0
    rw [hS', add_comm]; exact h5 _ _ _

theorem theta_form (hG : GlobalTheory.Published.GelfandKazhdanDual) (H : GlobalTheory.Published.CaraianiLocalGlobalDual) :
    GlobalTheory.Published.CaraianiLocalGlobal := fun E Ω _ _ _ _ _ _ l _ ι a ha π hc hcoh =>
  H E Ω l ι a ha π (dualIsConj_of_isCsd (hG E a π) hc) hcoh

theorem dualIsConj_iso {π π' : CuspSub L a} (h : π.Iso π') (hd : DualIsConj π) : DualIsConj π' := by
  obtain ⟨T, hT⟩ := h
  obtain ⟨B, h1, h2, h3, h4, h5⟩ := hd
  have hT' : ∀ o φ, T.symm (π'.op o φ) = π.op o (T.symm φ) := fun o φ => by
    rw [LinearEquiv.symm_apply_eq, hT, LinearEquiv.apply_symm_apply]
  refine ⟨B.compl₁₂ T.symm.toLinearMap T.symm.toLinearMap, fun φ h => ?_, fun ψ h => ?_, fun k φ ψ => ?_,
    fun k φ ψ => ?_, fun X φ ψ => ?_⟩
  · exact (map_eq_zero_iff _ T.symm.injective).1 (h1 _ fun x => by simpa using h (T x))
  · exact (map_eq_zero_iff _ T.symm.injective).1 (h2 _ fun x => by simpa using h (T x))
  · simp [hT', h3]
  · simp [hT', h4]
  · simp [hT', h5]

theorem central_eq_zero {π : CuspSub L a} (hd : DualIsConj π) {c : ℂ} (hc : ∀ φ, π.op (.lie (oneL L a)) φ = c • φ) :
    c = 0 := by
  obtain ⟨B, h1, -, -, -, h5⟩ := hd
  have e : conjOp (.lie (oneL L a)) = (.lie (oneL L a) : Op L a) := by
    change Op.lie _ = _
    congr 1
    funext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  by_contra hne
  refine h0 (congrArg Subtype.val (h1 ⟨φ, hφ⟩ fun ψ => ?_))
  have := h5 (oneL L a) ⟨φ, hφ⟩ ψ
  rw [e, hc, hc, map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, ← two_mul] at this
  simpa [hne] using this

variable (Ω : Type) [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ)

theorem compat_of (H : GlobalTheory.Published.CaraianiLocalGlobalDual) (ha : 2 ≤ a) (π : CuspSub L a) (hc : DualIsConj π)
    (hcoh : GKCoh.IsCohomological π) : ∃ R, Compat Ω ι π R := H L Ω l ι a ha π hc hcoh

theorem triv_all : DualIsConj (CuspSub.triv L (le_refl 1)) ∧ GKCoh.IsCohomological (CuspSub.triv L (le_refl 1)) ∧
    Compat Ω ι (CuspSub.triv L (le_refl 1)) 1 := by
  refine ⟨?_, ⟨_, GKCoh.isCohFor_triv le_rfl⟩, compat_triv Ω ι⟩
  have h := GlobalTheory.ContraPair.Model.polarizedPair_triv (L := L).dual
  rwa [pow_one, GlobalTheory.GalOfCusp.compNorm_quadChar, dualIsConjBy_one] at h

end GlobalTheory.LocGlobDual.Model

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ExistsPrimeNotMem
section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.LocLanglands GlobalTheory.WeilDeligne Polynomial TensorProduct Module
open GlobalTheory.Published.ParamAboveModel

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published.CharWDTest

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

omit [NumberField E] [IsAlgClosure E Ω] in

theorem exists_prime_notMem (w : HeightOneSpectrum (𝓞 E)) : ∃ p : ℕ, p.Prime ∧ ((p : ℕ) : 𝓞 E) ∉ w.asIdeal := by
  by_cases h2 : ((2 : ℕ) : 𝓞 E) ∈ w.asIdeal
  · refine ⟨3, Nat.prime_three, fun h3 => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)⟩
    have := w.asIdeal.sub_mem h3 h2
    norm_num at this
    exact this
  · exact ⟨2, Nat.prime_two, h2⟩

theorem comp_eq {art : Ideles E →* Gab E Ω} (hart : IsGlobalArtin art) {χ : HChar E} {n : (E →+* ℂ) → ℤ}
    (hn : IsAlgPos χ n) {ξ : (w.adicCompletion E)ˣ →* ℂˣ} (hξ : GlobalTheory.NPin.IsComp χ w ξ)
    {a a' : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h a) (ha' : IsLocalArtin h a') :
    ξ.comp a = ξ.comp a' := by
  obtain rfl := eq_loc hξ
  obtain ⟨p, hp, hw⟩ := exists_prime_notMem w
  have := Fact.mk hp
  obtain ⟨ι⟩ : Nonempty (Qbar p ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex p
  obtain ⟨r, -, hr⟩ := hart.exists_isLAdicOf ι hn
  ext σ
  have h1 := hr.loc_away (Or.inl hw) _ _ (ha.glob art hart σ)
  have h2 := hr.loc_away (Or.inl hw) _ _ (ha'.glob art hart σ)
  exact ι.symm.injective (h1.symm.trans h2)

theorem of_parameter (hL : LocalLanglandsGL) (H : HeckeLAdicParameterAbove) : AlgebraicCharacterWD := by
  intro E Ω _ _ _ _ _ l _ P AI hT ι art hart χ n μ hn hμ hLa w A h O _ _ _ Bw hj ξ hξ a ha
  obtain ⟨rc, hrc⟩ := (hL.1 E Ω A w h).exists
  obtain ⟨a', ha', hs, e⟩ := rhs_eq h hξ hrc
  rw [H E Ω l P AI hT ι art hart χ n μ hn hμ hLa w A h O Bw hj ξ hξ rc hrc, e]
  obtain rfl := eq_loc hξ
  congr 1
  exact comp_eq hart hn hξ ha' ha

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (ι : Om l ≃+* ℂ)
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : GlobalTheory.Pst.Induces Bw)

theorem lpOfChar_inj {ξ ξ' : Weil h →* ℂˣ} {hξ hξ'} (e : WD.lpOfChar h ξ hξ = WD.lpOfChar h ξ' hξ') : ξ = ξ' := by
  ext σ
  have := congrArg (fun x => WD.eig x σ) e
  simpa only [eig_lpOfChar, Multiset.singleton_inj] using this

theorem isPstAt_of_eq {r : ↥(Dec (F := E) A) →* GL (Fin 1) (Om l)} {ξ : (w.adicCompletion E)ˣ →* ℂˣ}
    {a : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h a) {hs} (hξ : ξ ≠ 1)
    (e : wdAt P ι Bw h hj r = WD.lpOfChar h (ξ.comp a) hs) : IsPstAt P Bw r := by
  by_contra hr
  rw [wdAt_of_not_isPstAt ι Bw h hj hr] at e
  refine hξ (MonoidHom.ext fun x => ?_)
  obtain ⟨σ, rfl⟩ := ha.surj x
  have h1 := congrArg (fun x => WD.eig x σ) e
  simp only [eig_lpOfChar, trivWD] at h1
  have h2 : (WDRep.diag h fun _ : Fin 1 => (1 : ℂˣ)).ρ σ = 1 := by
    ext; simp [WDRep.diag]
  rw [WD.eig_mk, h2] at h1
  have h3 : ((ξ.comp a σ : ℂˣ) : ℂ) ∈ (LinearMap.charpoly (1 : End ℂ (Fin 1 → ℂ))).roots := by
    rw [h1]; simp
  rw [mem_roots (LinearMap.charpoly_monic _).ne_zero, ← End.hasEigenvalue_iff_isRoot_charpoly] at h3
  obtain ⟨u, hu⟩ := h3.exists_hasEigenvector
  have h4 := hu.apply_eq_smul
  rw [End.one_apply] at h4
  have h5 : ((ξ.comp a σ : ℂˣ) : ℂ) = 1 := smul_left_injective ℂ hu.2 (h4.symm.trans (one_smul _ _).symm)
  exact Units.ext h5

theorem holds_abs' (hB : DeRhamPotSemistable) (hT : Nonempty (LocTied l P AI))
    {art : Ideles E →* Gab E Ω} (hart : IsGlobalArtin art)
    {μ : G E Ω →* (Qbar l)ˣ} (hμ : Continuous μ)
    (hL : IsLAdicOf art ι (Model.absPow E (1 : ℕ)) (fun _ => ((1 : ℕ) : ℤ)) μ)
    {ξ : (w.adicCompletion E)ˣ →* ℂˣ} (hξ : GlobalTheory.NPin.IsComp (Model.absPow E (1 : ℕ)) w ξ)
    {a : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h a) :
    wdAt P ι Bw h hj ((rk1 μ).comp (Dec (F := E) A).subtype) = WD.lpOfChar h (ξ.comp a) (ha.smooth hξ.1) := by
  obtain ⟨T⟩ := hT
  refine CharWDModel.holds_abs P ι Bw h hj hart hμ hL (hB.isPstAt T Bw _ ?_
    (CharAboveModel.conclusion_absPow P AI ⟨T⟩ ι art hart 1 μ hμ hL A O Bw).1) hξ ha
  refine continuous_matrix fun i j => ?_
  have : Continuous fun g : Dec (F := E) A => ((μ g : (Qbar l)ˣ) : Qbar l) :=
    Units.continuous_val.comp (hμ.comp continuous_subtype_val)
  fin_cases i; fin_cases j
  simpa [rk1] using this

theorem ne_inv {x : WD h} {ξ : (w.adicCompletion E)ˣ →* ℂˣ} {a : Weil h →* (w.adicCompletion E)ˣ}
    (ha : IsLocalArtin h a) {hs hs'} (e : x = WD.lpOfChar h (ξ.comp a) hs) (hξ : ξ ≠ ξ⁻¹) :
    x ≠ WD.lpOfChar h (ξ⁻¹.comp a) hs' := fun e' => by
  have := lpOfChar_inj (e.symm.trans e')
  refine hξ (MonoidHom.ext fun y => ?_)
  obtain ⟨σ, rfl⟩ := ha.surj y
  exact DFunLike.congr_fun this σ

omit [IsAlgClosure E Ω] in

theorem abs_ne_inv : (Model.absPow E (1 : ℕ)).loc w ≠ ((Model.absPow E (1 : ℕ)).loc w)⁻¹ := fun e => by
  have hval := (Model.absPow_isAbsPow E (1 : ℕ)).2.1 w
  have h1 : (Model.absPow E (1 : ℕ)).val w = ((Model.absPow E (1 : ℕ)).val w)⁻¹ :=
    DFunLike.congr_fun e (atFin w (unif w))
  have h2 := congrArg (fun u : ℂˣ => (u : ℂ)) h1
  simp only [Units.val_inv_eq_inv_val, hval] at h2
  have hq : 1 < Ideal.absNorm w.asIdeal := by
    simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using GlobalTheory.WeilDeligne.one_lt_normV w
  simp only [Nat.cast_one, Complex.ofReal_one, Complex.cpow_neg_one, inv_inv] at h2
  have h0 : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h3 := mul_inv_cancel₀ h0
  rw [h2] at h3
  have h4 : Ideal.absNorm w.asIdeal * Ideal.absNorm w.asIdeal = 1 := by exact_mod_cast h3
  nlinarith

end GlobalTheory.Published.CharWDTest

end
end

