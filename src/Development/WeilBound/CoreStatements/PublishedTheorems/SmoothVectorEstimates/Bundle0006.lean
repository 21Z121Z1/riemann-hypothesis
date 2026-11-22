import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0356
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.SatakeEigenvalues

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.MirrorMap
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace MirrorMap

theorem mir_map {R S : Type} [CommRing R] [CommRing S] {a m : ℕ} (p : R →+* S) {γ : GL (Fin a) R}
    (h : Mir m γ) : Mir m (GeneralLinearGroup.map p γ) := by
  intro i k hik
  change p (γ.val i k) = _
  rw [h i k hik, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem mirS_mul (h10 : MirabolicColumnBlock) {S : Finset (Pl E)} {x g : GA E a} (hx : Mir (a - 1) x) (hg : MirS S g) :
    MirS S (x * g) := by
  refine ⟨?_, fun w hw => ?_⟩
  · rw [map_mul]
    exact (h10 _ a (a - 1)).2.2.2.2.1 _ _ (mir_map (pInf E) hx) hg.1
  · rw [map_mul]
    exact (h10 _ a (a - 1)).2.2.2.2.1 _ _ (mir_map ((pLoc E w).comp (pFin E)) hx) (hg.2 w hw)

end MirrorMap

theorem mirror_global_of : MirabolicColumnBlock → G0 → G5 → G9 → PlacewiseToOutsideS → FourierUniquenessMirabolic → WeakApproximationGL → WhittakerVanishingImpliesZero := by
  intro h10 h0 h5 h9 h9b h11 h12 E _ _ _ a ψ hψ S hcond φ hgood hleft hsat hvan
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hproj, -⟩ := h0 E a
  have hcont : Continuous (Wh ψ φ) := ((h5 E a ψ hψ).2.2.2 φ hgood).1
  have step1 : ∀ g, MirS S g → Wh ψ φ g = 0 := by
    intro g hg
    obtain ⟨g₀, e1, e2, e3⟩ := hproj S g
    refine h9b E a S (Wh ψ φ) hcont ?_ g g₀ e1 e2 e3 ?_
    · intro w hw h hh hz u
      obtain ⟨B, hB⟩ := hsat w hw
      exact h9 E a ψ hψ w (hcond w hw) B φ hgood hB h hh hz u
    · refine hvan g₀ ⟨?_, fun w hw => ?_⟩ e3
      · rw [e1]; exact hg.1
      · rw [e2 w hw]; exact hg.2 w hw
  have step2 : ∀ g, MirS S g → φ g = 0 := by
    intro g hg
    refine h11 E a ψ hψ (a - 1) φ (by omega) hgood {g | MirS S g} ?_ ?_ step1 g hg
    · intro γ hγ g hg
      exact MirrorMap.mirS_mul h10 (MirrorMap.mir_map (algebraMap E (Ad E)) hγ) hg
    · intro k hk y g hg
      exact MirrorMap.mirS_mul h10 ((h10 (Ad E) a (a - 1)).2.2.2.2.2.1 k y hk) hg
  have hEq : (⇑φ) = fun _ => (0 : ℂ) := by
    refine Continuous.ext_on (h12 E a S) φ.continuous continuous_const ?_
    rintro x ⟨γ, g, rfl, hg1, hg2⟩
    show φ (ratGL E a γ * g) = 0
    rw [hleft]
    refine step2 g ⟨?_, fun w hw => ?_⟩
    · rw [hg1]; exact (h10 _ a (a - 1)).2.2.1
    · rw [hg2 w hw]; exact (h10 _ a (a - 1)).2.2.1
  ext x
  simpa using congrFun hEq x

end PositivityTheory.jumpWindows

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.PSmoNorm
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

theorem smonorm_of : Meet → CuspidalIrreducibleSubrep → SmoNorm := by
  intro hM hG E _ _ _ a π π' hπ hπ' hS
  let μ : Measure (GA E a) := Measure.haar
  have : μ.IsMulRightInvariant := GlobalTheory.CovolGL.isMulRightInvariant E a μ
  obtain ⟨H, hH, hf⟩ := hG E a μ π hπ
  obtain ⟨H', hH', hf'⟩ := hG E a μ π' hπ'
  have hne : H ⊓ H' ≠ ⊥ := hM E a μ π π' H H' hπ hπ' hH.1 hH'.1
    (fun φ hφ => ⟨hf.finitePartMemL2 φ hφ, hf.classes_le (toL2_mem_classes hφ (hf.finitePartMemL2 φ hφ))⟩)
    (fun φ hφ => ⟨hf'.finitePartMemL2 φ hφ, hf'.classes_le (toL2_mem_classes hφ (hf'.finitePartMemL2 φ hφ))⟩) hS
  have h1 : H ⊓ H' = H := (hH.2.2 _ inf_le_left (hH.1.inf hH'.1)).resolve_left hne
  have h2 : H ⊓ H' = H' := (hH'.2.2 _ inf_le_right (hH.1.inf hH'.1)).resolve_left hne
  have e : H = H' := h1.symm.trans h2
  subst e
  exact hf.unique hf'

end PositivityTheory.jumpWindows

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.SmoothVectorOrbit
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace SmoothVectorOrbit

theorem orb_smul {ι : Type} [Fintype ι] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) (c : ℂ) (v : X) :
    orb ρ (c • v) = c • orb ρ v := by
  funext M
  simp only [PositivityTheory.jumpWindows.orb, Pi.smul_apply]
  split_ifs <;> simp

theorem smV_smul {ι : Type} [Fintype ι] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) (c : ℂ) (v : X) (h : SmV ρ v) : SmV ρ (c • v) := by
  unfold PositivityTheory.jumpWindows.SmV at h ⊢
  rw [PositivityTheory.jumpWindows.SmoothVectorOrbit.orb_smul]
  exact h.const_smul c

end SmoothVectorOrbit

theorem smooth_vector_orbit_invariance : G0 → G5 → G5b → G9 → PlacewiseToOutsideS → G8 := by
  intro hAC hSW hSP hWS hWV
  unfold PositivityTheory.jumpWindows.G8 PositivityTheory.jumpWindows.ForE
  intro E _ _ _ a ψ hψ S hS Y hY φ hφY hφ0 hφsm hφsph hφeig
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hreg, -⟩ := hAC E a
  obtain ⟨hΛ, htr, -, hW⟩ := hSW E a ψ hψ
  obtain ⟨hsmooth, hsph, hsph_smul, -, -⟩ := hSP E a S
  obtain ⟨-, hYtr, hYmir⟩ := hY
  obtain ⟨hWcont, hWne, -⟩ := hW φ (hYmir φ hφY)
  obtain ⟨g, hg⟩ := hWne hφ0
  obtain ⟨g₀, harch, hloc, hsupp⟩ := hreg S g
  have hg₀ : PositivityTheory.jumpWindows.Wh ψ φ g₀ ≠ 0 := by
    intro h0
    refine hg (hWV E a S _ hWcont ?_ g g₀ harch hloc hsupp h0)
    intro w hw h hh h0' u
    obtain ⟨B, hB⟩ := hφeig w hw
    exact hWS E a ψ hψ w (hS w hw) B φ (hYmir φ hφY) hB h hh h0' u
  have hφ'Y : PositivityTheory.jumpWindows.Rt E a g₀ φ ∈ Y := hYtr g₀ hsupp φ hφY
  have hW1 : PositivityTheory.jumpWindows.Wh ψ (PositivityTheory.jumpWindows.Rt E a g₀ φ) 1 ≠ 0 := by
    rw [htr, one_mul]
    exact hg₀
  refine ⟨(PositivityTheory.jumpWindows.Wh ψ (PositivityTheory.jumpWindows.Rt E a g₀ φ) 1)⁻¹ •
      PositivityTheory.jumpWindows.Rt E a g₀ φ, Y.smul_mem _ hφ'Y, ?_, ?_, ?_⟩
  · exact PositivityTheory.jumpWindows.SmoothVectorOrbit.smV_smul _ _ _ (hsmooth g₀ φ hφsm)
  · exact hsph_smul _ _ (hsph g₀ φ hφsph)
  · obtain ⟨Λ, hΛ1⟩ := hΛ 1
    rw [← hΛ1 _ (hYmir _ (Y.smul_mem _ hφ'Y)), map_smul, hΛ1 _ (hYmir _ hφ'Y), smul_eq_mul,
      inv_mul_cancel₀ hW1]

end PositivityTheory.jumpWindows

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.UnipotentCharacter
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace UnipotentCharacter

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def chi (ψ : AddChar (Ad E) ℂ) (w : Pl E) : AddChar (w.adicCompletion E) ℂ where
  toFun y := ψ (sFin E (sLoc E w y))
  map_zero_eq_one' := by simp only [map_zero, AddChar.map_zero_eq_one]
  map_add_eq_mul' x y := by simp only [map_add, AddChar.map_add_eq_mul]

theorem chi_apply (ψ : AddChar (Ad E) ℂ) (w : Pl E) (y : w.adicCompletion E) :
    chi ψ w y = ψ (sFin E (sLoc E w y)) := rfl

theorem chi_cont {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (w : Pl E) : Continuous (chi ψ w) :=
  hψ.cont.comp ((continuous_const.prodMk continuous_id : Continuous fun x : Af E =>
    ((0, x) : InfiniteAdeleRing E × Af E)).comp (CuspSub.continuous_sLoc w))

theorem lastE_loc (w : Pl E) {k : ℕ} (y : UnipotentBlockColumnIndex a k k → w.adicCompletion E) :
    lastE k (fun t => sFin E (sLoc E w (y t))) = sFin E (sLoc E w (lastE k y)) := by
  unfold lastE
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs <;> simp

theorem sum_of {X : Type} [AddCommMonoid X] [Module ℂ X] (P : X → Prop) (h0 : P 0)
    (hadd : ∀ x y, P x → P y → P (x + y)) (hsm : ∀ (c : ℂ) x, P x → P (c • x)) {ι : Type}
    (T : Finset ι) (c : ι → ℂ) (f : ι → X) (hf : ∀ t, P (f t)) : P (∑ t ∈ T, c t • f t) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using h0
  | insert t T ht ih => rw [Finset.sum_insert ht]; exact hadd _ _ (hsm _ _ (hf t)) ih

end UnipotentCharacter

open UnipotentCharacter in
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in
theorem whittaker_expansion_cuspidal : S2 → S9 → MirabolicColumnBlock → G0 → G5 → G5b → G7 := by
  intro hS2 hS9 hS10 hG0 hG5 hG5b E _ _ _ a ψ hψ S Y Y' hY hY' n m w hw hmw hSt
  obtain ⟨φ, hφY, φ', hφY', hsm, hsm', hlev, hlev', h1, hWh⟩ := hSt
  obtain ⟨-, -, i3, i4, i5, -, -, i8, -, i10, -⟩ := hG0 E a
  obtain ⟨g5a, g5r, -, g5c⟩ := hG5 E a ψ hψ
  obtain ⟨b1, b2, b3, b4, b5⟩ := hG5b E a S
  obtain ⟨s10dec, -, -, s10blk1, -⟩ := hS10 (w.adicCompletion E) a (m w + 1)
  have hpoly : PolyBd (repI E a) := ⟨1, 0, zero_le_one, fun g x => by
    rw [pow_zero, mul_one, one_mul]
    exact le_of_eq (norm_Rt (infGL E a g) x)⟩
  obtain ⟨s0, sadd, ssmul, -, -, -⟩ := hS2 (InfinitePlace E) a (XB E a) (repI E a) hpoly
  let U : Set (GL (Fin a) (w.adicCompletion E)) := {u | repW a w u φ = φ} ∩ {u | repW a w u φ' = φ'}
  have hU : U ∈ 𝓝 (1 : GL (Fin a) (w.adicCompletion E)) := Filter.inter_mem (hlev w hw) (hlev' w hw)
  have hne : ∃ x, chi ψ w x ≠ 1 := by
    obtain ⟨y, hy⟩ := hψ.loc w
    exact ⟨y, hy⟩
  obtain ⟨T, c, η, r, hη1, hr1, hrMir, -, -, hmain⟩ :=
    hS9 (w.adicCompletion E) a (m w) hmw (chi ψ w) (chi_cont hψ w) hne (XB E a) (repW a w) U hU
  have inS : ∀ u, InS S (fl a w u : GA E a) := fun u v hv => i5 w v u (fun e => hv (e ▸ hw))
  have stab : ∀ Z : Submodule ℂ (XB E a), YOK ψ S Z → ∀ u, ∀ x ∈ Z, repW a w u x ∈ Z :=
    fun Z hZ u x hx => hZ.stable _ (inS u) x hx
  have memZ : ∀ Z : Submodule ℂ (XB E a), YOK ψ S Z → ∀ x ∈ Z, ∑ t ∈ T, c t • repW a w t x ∈ Z :=
    fun Z hZ x hx => Z.sum_mem fun t _ => Z.smul_mem _ (stab Z hZ t x hx)
  have smZ : ∀ x : XB E a, SmV (repI E a) x → SmV (repI E a) (∑ t ∈ T, c t • repW a w t x) :=
    fun x hx => sum_of _ s0 sadd ssmul T c _ fun t => b1 _ x hx
  have levZ : ∀ x : XB E a, Lev S x → Lev S (∑ t ∈ T, c t • repW a w t x) :=
    fun x hx => sum_of _ b5 b4 b3 T c _ fun t => b2 _ x hx

  have key : ∀ Z : Submodule ℂ (XB E a), YOK ψ S Z → ∀ x ∈ Z, (∀ u ∈ U, repW a w u x = x) →
      ∀ g' : GA E a, cLoc w g' = 1 → ∀ h, GlobalTheory (m w + 1) h →
      Wh ψ (∑ t ∈ T, c t • repW a w t x) (g' * fl a w h) = η h * Wh ψ x (g' * fl a w (r h)) := by
    intro Z hZ x hx hxU g' hg' h hh
    obtain ⟨Λ, hΛ⟩ := g5a g'
    have hcond : ∀ z ∈ Z, ∀ y : UnipotentBlockColumnIndex a (m w + 1) (m w + 1) → w.adicCompletion E,
        (Λ : XB E a →ₗ[ℂ] ℂ) (repW a w (blkU y) z) = chi ψ w (lastE (m w + 1) y) * (Λ : XB E a →ₗ[ℂ] ℂ) z := by
      intro z hz y
      show Λ _ = _ * Λ _
      rw [hΛ _ (hZ.good _ (stab Z hZ _ z hz)),
        hΛ _ (hZ.good _ hz), repW_apply, g5r, i8 w g' hg', i10,
        (g5c z (hZ.good _ hz)).2.2 (m w + 1) (Nat.succ_pos _), lastE_loc, chi_apply]
    have := hmain x hxU Z (stab Z hZ) hx (Λ : XB E a →ₗ[ℂ] ℂ) hcond h hh
    change Λ _ = η h * Λ _ at this
    rw [hΛ _ (hZ.good _ (stab Z hZ _ _ (memZ Z hZ x hx))), hΛ _ (hZ.good _ (stab Z hZ _ _ hx)),
      repW_apply, repW_apply, g5r, g5r] at this
    exact this
  refine ⟨_, memZ Y hY φ hφY, _, memZ Y' hY' φ' hφY', smZ φ hsm, smZ φ' hsm', levZ φ hlev, levZ φ' hlev', ?_, ?_⟩
  · have := key Y hY φ hφY (fun u hu => hu.1) 1 (map_one _) 1 s10blk1
    rw [hr1] at this
    simp only [map_one, mul_one] at this
    rw [this]
    exact mul_ne_zero hη1 h1
  · intro g hg
    obtain ⟨hgI, hgL⟩ := hg
    have hgw : Mir (m w + 1) (cLoc w g) := by simpa using hgL w
    obtain ⟨y, h, hh, hdec⟩ := s10dec _ hgw
    set g' : GA E a := g * (fl a w (cLoc w g))⁻¹ with hg'def
    have hg' : cLoc w g' = 1 := by rw [hg'def, map_mul, map_inv, i4, mul_inv_cancel]
    have red : ∀ Z : Submodule ℂ (XB E a), YOK ψ S Z → ∀ x ∈ Z, (∀ u ∈ U, repW a w u x = x) →
        Wh ψ (∑ t ∈ T, c t • repW a w t x) g =
          ψ (lastE (m w + 1) fun t => sFin E (sLoc E w (y t))) * (η h * Wh ψ x (g' * fl a w (r h))) := by
      intro Z hZ x hx hxU
      have e : g = blkU (fun t => sFin E (sLoc E w (y t))) * (g' * fl a w h) := by
        rw [← i10, ← mul_assoc, ← i8 w g' hg', mul_assoc, ← map_mul, ← hdec, hg'def, inv_mul_cancel_right]
      rw [e, (g5c _ (hZ.good _ (memZ Z hZ x hx))).2.2 (m w + 1) (Nat.succ_pos _), key Z hZ x hx hxU g' hg' h hh]
    rw [red Y hY φ hφY (fun u hu => hu.1), red Y' hY' φ' hφY' (fun u hu => hu.2)]
    by_cases hη : η h = 0
    · rw [hη]; simp
    congr 2
    refine hWh _ ⟨?_, fun v => ?_⟩
    · rw [map_mul, hg'def, map_mul, map_inv, i3, i3, inv_one, mul_one, mul_one]
      exact hgI
    · rcases eq_or_ne v w with rfl | hv
      · rw [map_mul, hg', i4, one_mul]
        exact hrMir h hh hη
      · rw [map_mul, hg'def, map_mul, map_inv, i5 w v _ hv, i5 w v _ hv, inv_one, mul_one, mul_one]
        simpa [hv] using hgL v

end PositivityTheory.jumpWindows

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WeilJacquetShalikaLaw
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.jumpWindows

namespace WeilJacquetShalikaLaw

section Loc

variable {F : Type} [Field F] {a : ℕ}

def WS (χ : AddChar F ℂ) (a : ℕ) : Submodule ℂ (GL (Fin a) F → ℂ) where
  carrier := {W | ∀ n ∈ GroundTheory.Automorphic.Iwasawa.unipotent F a, ∀ g,
    W (n * g) = GroundTheory.Automorphic.Whittaker.psiN χ n * W g}
  add_mem' {W W'} hW hW' n hn g := by
    simp only [Pi.add_apply, hW n hn g, hW' n hn g, mul_add]
  zero_mem' n hn g := by simp
  smul_mem' c W hW n hn g := by
    simp only [Pi.smul_apply, smul_eq_mul, hW n hn g]
    ring

theorem WS_stable (χ : AddChar F ℂ) (a : ℕ) :
    ∀ g, ∀ v ∈ WS χ a, GlobalTheory.PRep.rightReg ℂ (GL (Fin a) F) ℂ g v ∈ WS χ a := by
  intro g v hv n hn x
  change v (n * x * g) = _ * v (x * g)
  rw [mul_assoc]
  exact hv n hn _

def rhoW (χ : AddChar F ℂ) (a : ℕ) : Representation ℂ (GL (Fin a) F) (WS χ a) :=
  GlobalTheory.PRep.sub (GlobalTheory.PRep.rightReg ℂ (GL (Fin a) F) ℂ) (WS χ a) (WS_stable χ a)

@[simp] theorem rhoW_apply (χ : AddChar F ℂ) (g x : GL (Fin a) F) (v : WS χ a) :
    (rhoW χ a g v : GL (Fin a) F → ℂ) x = (v : GL (Fin a) F → ℂ) (x * g) := rfl

def ev (χ : AddChar F ℂ) (a : ℕ) : WS χ a →ₗ[ℂ] ℂ :=
  (LinearMap.proj (R := ℂ) (φ := fun _ : GL (Fin a) F => ℂ) 1).comp (WS χ a).subtype

theorem ev_apply (χ : AddChar F ℂ) (v : WS χ a) : ev χ a v = (v : GL (Fin a) F → ℂ) 1 := rfl

theorem sd_eq (M : Matrix (Fin a) (Fin a) F) :
    GroundTheory.Automorphic.Whittaker.superdiagSum M = ∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, M p.1 p.2 := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  rfl

end Loc

theorem exists_unit_one_add_generator {a : ℕ} (B : Multiset ℂˣ) (hB : B.card = a) : ∃ z : Fin a → ℂˣ, B = Finset.univ.val.map z := by
  subst hB
  refine ⟨fun i => B.toList.get ⟨i, by simp⟩, ?_⟩
  rw [Fin.univ_val_map]
  conv_lhs => rw [← Multiset.coe_toList B]
  congr 1
  refine List.ext_get (by simp) fun n h1 h2 => ?_
  simp

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def psiW (ψ : AddChar (Ad E) ℂ) (w : Pl E) : AddChar (w.adicCompletion E) ℂ :=
  ψ.compAddMonoidHom ((sFin E).toAddMonoidHom.comp (sLoc E w).toAddMonoidHom)

theorem psiOK {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) {w : Pl E} (hc : Cond ψ w) :
    PositivityTheory.JacquetShalikaLocal.PsiOK (psiW ψ w) := by
  obtain ⟨h1, ϖ, y, hϖ, hy, hne⟩ := hc
  refine ⟨fun x hx => h1 x (by rw [← PositivityTheory.JacquetShalikaLocal.SatakeEigenvalues.O_eq w]; exact hx), ⟨y, ?_, hne⟩, fun x => hψ.norm _⟩
  refine (SetLike.ext_iff.1 (PositivityTheory.JacquetShalikaLocal.SatakeEigenvalues.O_eq w) _).2 ?_
  have hu := PositivityTheory.JacquetShalikaLocal.SatakeEigenvalues.isUnifV_uniformizer w
  change Valued.v (_ * y) ≤ 1
  change Valued.v (ϖ * y) ≤ 1 at hy
  rw [map_mul] at hy ⊢
  rw [hu]
  rw [hϖ] at hy
  exact hy

theorem dot_eLast {k : ℕ} (y : UnipotentBlockColumnIndex a k k → Ad E) : dot (eLast a k) y = lastE k y := by
  simp only [dot, eLast, lastE]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs <;> simp

theorem law [IsTotallyComplex E] {ψ : AddChar (Ad E) ℂ} {f : GA E a → ℂ}
    (hf : ∀ k, 0 < k → ∀ (y : UnipotentBlockColumnIndex a k k → Ad E) g, f (blkU y * g) = ψ (lastE k y) * f g)
    (w : Pl E) (n : GL (Fin a) (w.adicCompletion E)) (hn : n ∈ GroundTheory.Automorphic.Iwasawa.unipotent _ a)
    (g : GA E a) : f (fl a w n * g) = GroundTheory.Automorphic.Whittaker.psiN (psiW ψ w) n * f g := by
  obtain ⟨t1, t2, t3⟩ := GlobalTheory.T.localUpperUnipotent_adelic_upperUnipotent E a w n (fun i j hij => hn.1 hij) hn.2
  have := GlobalTheory.T.whittakerLaw_upperTriangularUnipotent_adelic E a ψ f (fun k hk y g => by rw [dot_eLast]; exact hf k hk y g) _ t1 t2 g
  change f (finGL E a (locGL E a w n) * g) = _
  rw [this, t3, GroundTheory.Automorphic.Whittaker.psiN, sd_eq]
  rfl

theorem whitW (w : Pl E) (χ : AddChar (w.adicCompletion E) ℂ) :
    PositivityTheory.JacquetShalikaLocal.Whit (rhoW χ a) χ (ev χ a) := by
  intro g hg u
  rw [ev_apply, ev_apply, rhoW_apply, one_mul]
  have := u.2 g hg 1
  rwa [mul_one] at this

end WeilJacquetShalikaLaw

theorem whittaker_uniqueness_local : PositivityTheory.JacquetShalikaLocal.L7 → PositivityTheory.JacquetShalikaLocal.lift_levelP_alt₂ → G0 → G5 → G9 := by
  intro hL7 hL12 hG0 hG5 E _ _ _ a ψ hψ w hc B φ hφ hsat h hh hWh u
  have hcomm := (hG0 E a).2.2.2.2.2.2.2.1 w h hh
  obtain ⟨hΛ, hrt, hgood, hreg⟩ := hG5 E a ψ hψ
  rcases hsat with rfl | hsat
  · obtain ⟨Λ, hΛ'⟩ := hΛ (h * fl a w u)
    rw [← hΛ' 0 hφ, map_zero]
  obtain ⟨z, hz⟩ := WeilJacquetShalikaLaw.exists_unit_one_add_generator B hsat.2.2.1
  let v : GL (Fin a) (w.adicCompletion E) → ℂ := fun x => Wh ψ φ (h * fl a w x)
  have hfix : ∀ k ∈ KGL w a, Rt E a (fl a w k) φ = φ := fun k hk => GlobalTheory.LGrp.mem_fixed.1 hsat.2.1 k hk
  have hv : v ∈ WeilJacquetShalikaLaw.WS (WeilJacquetShalikaLaw.psiW ψ w) a := by
    intro n hn x
    change Wh ψ φ (h * fl a w (n * x)) = _ * Wh ψ φ (h * fl a w x)
    rw [map_mul, ← mul_assoc, hcomm n, mul_assoc]
    exact WeilJacquetShalikaLaw.law (hreg φ hφ).2.2 w n hn _
  let vs : WeilJacquetShalikaLaw.WS (WeilJacquetShalikaLaw.psiW ψ w) a := ⟨v, hv⟩
  have hv1 : (vs : GL (Fin a) (w.adicCompletion E) → ℂ) 1 = 0 := by
    change Wh ψ φ (h * fl a w 1) = 0
    rw [map_one, mul_one]
    exact hWh
  by_cases h0 : vs = 0
  · exact congrFun (congrArg Subtype.val h0) u
  have hK := Final.GLintComm E w a
  have hsv : IsSatVecGL w (WeilJacquetShalikaLaw.rhoW (WeilJacquetShalikaLaw.psiW ψ w) a) vs (Finset.univ.val.map z) := by
    refine ⟨h0, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, by simp, fun ϖ hϖ j hj => ?_⟩
    · apply Subtype.ext
      funext x
      change Wh ψ φ (h * fl a w (x * k)) = Wh ψ φ (h * fl a w x)
      rw [map_mul, ← mul_assoc, ← hrt, hfix k hk]
    · rw [← hz]
      apply Subtype.ext
      have e := map_heckeVec (ρ := WeilJacquetShalikaLaw.rhoW (WeilJacquetShalikaLaw.psiW ψ w) a)
        (ρ' := GlobalTheory.PRep.rightReg ℂ (GL (Fin a) (w.adicCompletion E)) ℂ) hK (Tj_mem_hecke hϖ j) (WeilJacquetShalikaLaw.WS (WeilJacquetShalikaLaw.psiW ψ w) a).subtype (fun _ _ => rfl) vs
      rw [Submodule.subtype_apply, Submodule.subtype_apply] at e
      rw [e, Submodule.coe_smul]
      funext x
      obtain ⟨Λ, hΛ'⟩ := hΛ (h * fl a w x)
      have hfin := finite_heckeVec hK (Tj_mem_hecke hϖ j) (GlobalTheory.PRep.rightReg ℂ (GL (Fin a) (w.adicCompletion E)) ℂ) v
      have hfin2 := finite_heckeVec hK (Tj_mem_hecke hϖ j) (repW a w) φ
      have e1 := (LinearMap.proj (R := ℂ) (φ := fun _ : GL (Fin a) (w.adicCompletion E) => ℂ) x).toAddMonoidHom.map_finsum hfin
      have e2 := (Λ : XB E a →L[ℂ] ℂ).toLinearMap.toAddMonoidHom.map_finsum hfin2
      have e3 := hsat.2.2.2 ϖ hϖ j hj
      have key : ∀ c : GL (Fin a) (w.adicCompletion E) ⧸ KGL w a,
          (Tj ℂ a (Ov E w) ϖ j c.out • GlobalTheory.PRep.rightReg ℂ (GL (Fin a) (w.adicCompletion E)) ℂ c.out v) x =
            Λ (Tj ℂ a (Ov E w) ϖ j c.out • repW a w c.out φ) := by
        intro c
        rw [map_smul, hΛ' (repW a w c.out φ) (hgood φ (fl a w c.out) hφ)]
        change _ * v (x * c.out) = _ • Wh ψ (Rt E a (fl a w c.out) φ) (h * fl a w x)
        rw [hrt, smul_eq_mul]
        change _ * Wh ψ φ (h * fl a w (x * c.out)) = _
        rw [map_mul, mul_assoc]
      have LHS : heckeVec (GlobalTheory.PRep.rightReg ℂ (GL (Fin a) (w.adicCompletion E)) ℂ) (KGL w a)
          (Tj ℂ a (Ov E w) ϖ j) v x = Λ (heckeVec (repW a w) (KGL w a) (Tj ℂ a (Ov E w) ϖ j) φ) := by
        rw [heckeVec, heckeVec]
        exact e1.trans ((finsum_congr key).trans e2.symm)
      refine LHS.trans ?_
      rw [e3, map_smul, hΛ' φ hφ]
      rfl
  have heig := (hL12 E w).2 a _ (WeilJacquetShalikaLaw.rhoW (WeilJacquetShalikaLaw.psiW ψ w) a) vs z hsv
  have := hL7 (w.adicCompletion E) (WeilJacquetShalikaLaw.psiW ψ w) (WeilJacquetShalikaLaw.psiOK hψ hc) a _ (WeilJacquetShalikaLaw.rhoW (WeilJacquetShalikaLaw.psiW ψ w) a) vs z heig
    (WeilJacquetShalikaLaw.ev _ a) (WeilJacquetShalikaLaw.whitW w _) u
  rw [WeilJacquetShalikaLaw.ev_apply, WeilJacquetShalikaLaw.ev_apply, WeilJacquetShalikaLaw.rhoW_apply, one_mul, hv1, zero_mul] at this
  exact this

end PositivityTheory.jumpWindows

end
end

