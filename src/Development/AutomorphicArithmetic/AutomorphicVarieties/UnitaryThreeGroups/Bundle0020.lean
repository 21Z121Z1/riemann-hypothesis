import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0018
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0017
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.PtIneL
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0013
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0012
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0129
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0019

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.AdmissibleOfTypeII
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem cls_eq_one {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] (g : G ℚ Ω)
    (hg : ∀ ζ : Ω, ζ ^ N = 1 → g ζ = ζ) : Chr.cls ℚ Ω N g = 1 := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω N
  have h1 := Chr.cls_spec (k := ℚ) N g ζ hζ.pow_eq_one
  rw [hg ζ hζ.pow_eq_one] at h1
  have h2 : ζ ^ 1 = ζ ^ ((Chr.cls ℚ Ω N g : ZMod N)).val := by rw [pow_one]; exact h1
  have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.mpr ⟨N, Nat.pos_of_ne_zero (NeZero.ne N), hζ.pow_eq_one⟩
  rw [hfin.pow_eq_pow_iff_modEq, ← hζ.eq_orderOf] at h2
  ext
  rw [Units.val_one]
  have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h2
  rw [ZMod.natCast_val, ZMod.cast_id', id, Nat.cast_one] at this
  exact this.symm

private theorem block_form {k : Type} [Field k] (X : Matrix (Fin 3) (Fin 3) k) (Y : Matrix (Fin 2) (Fin 2) k)
    (hb : ∀ a b, Odd (wt a b) → X a b = 0) (h1 : X 1 1 = 1) (hY : Y = corner X) :
    X = !![Y 0 0, 0, Y 0 1; 0, 1, 0; Y 1 0, 0, Y 1 1] := by
  subst hY
  have e01 := hb 0 1 (by decide)
  have e10 := hb 1 0 (by decide)
  have e12 := hb 1 2 (by decide)
  have e21 := hb 2 1 (by decide)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [corner, e01, e10, e12, e21, h1]

private theorem conj_mat {Γ k : Type} [Group Γ] [Field k] (M : GL (Fin 3) k) (r : Γ →* GG 3 k) (g : Γ)
    (hg : (r g).right = 1) : (conjBy M r g).mat = (M : Matrix (Fin 3) (Fin 3) k) * (r g).mat * ((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := by
  have e : (conjBy M r g) = GG.ofGL M * r g * (GG.ofGL M)⁻¹ := rfl
  rw [e, GG.mat, ← map_inv]
  simp [SemidirectProduct.mul_left, SemidirectProduct.mul_right, hg, GG.mat, Units.val_mul]

private theorem eigvec {k : Type} [Field k] (M : GL (Fin 3) k) (X : Matrix (Fin 3) (Fin 3) k) (a : k)
    (h0 : ((M : Matrix (Fin 3) (Fin 3) k) * X * ((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) 0 0 = a)
    (h : ∀ i j, wt i j < 0 → ((M : Matrix (Fin 3) (Fin 3) k) * X * ((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) i j = 0) :
    X *ᵥ (((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ Pi.single 0 1) =
      a • (((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ Pi.single 0 1) := by
  set A := (M : Matrix (Fin 3) (Fin 3) k) * X * ((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) with hA
  set Mi := ((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)
  have hMi : Mi * (M : Matrix (Fin 3) (Fin 3) k) = 1 := by
    simp [Mi, ← Units.val_mul]
  have hXM : X * Mi = Mi * A := by
    rw [hA, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hMi, Matrix.one_mul]
  have hcol : A *ᵥ Pi.single 0 1 = a • Pi.single 0 1 := by
    have h10 : A 1 0 = 0 := h 1 0 (by simp [wt, wt1])
    have h20 : A 2 0 = 0 := h 2 0 (by simp [wt, wt1])
    ext i
    fin_cases i <;> simp [Matrix.mulVec_single, h0, h10, h20]
  rw [Matrix.mulVec_mulVec, hXM, ← Matrix.mulVec_mulVec, hcol, Matrix.mulVec_smul]

private theorem exists_two {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [hl : Fact l.Prime] (h2 : l ≠ 2)
    (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) :
    ∃ s ∈ Ine (F := ℚ) A, ∀ n : ℤ, cycBar ℚ Ω l s ^ n = 1 → n = 0 := by
  have hnd : ¬ ((l : ℤ) ∣ 2) := by
    intro hd
    have := Int.le_of_dvd (by norm_num) hd
    have hle : l ≤ 2 := by exact_mod_cast this
    have := hl.out.two_le
    omega
  have hu : IsUnit (2 : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    have a1 := PadicInt.norm_le_one (2 : ℤ_[l])
    have a2 : ¬ ‖((2 : ℤ) : ℤ_[l])‖ < 1 := by rw [PadicInt.norm_int_lt_one_iff_dvd]; exact hnd
    push_cast at a2
    exact le_antisymm a1 (not_lt.mp a2)
  obtain ⟨s, hs, hsv⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA hu.unit
  refine ⟨s, hs, fun n hn => ?_⟩
  have hinj : Function.Injective ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom) :=
    (algebraMap ℚ_[l] (Qbar l)).injective.comp Subtype.val_injective
  have hpow : hu.unit ^ n = 1 := by
    apply Units.map_injective (f := ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom) hinj
    rw [map_zpow, map_one, ← hsv]
    exact hn
  have hq : ((2 : ℚ) : ℚ_[l]) ^ n = 1 := by
    have := congrArg (fun x : ℤ_[l]ˣ => ((Units.map (PadicInt.Coe.ringHom (p := l)).toMonoidHom x : ℚ_[l]ˣ) : ℚ_[l])) hpow
    simp only [map_zpow, map_one, Units.val_one, Units.val_zpow_eq_zpow_val, Units.coe_map, IsUnit.unit_spec] at this
    have e : (PadicInt.Coe.ringHom (p := l)) (2 : ℤ_[l]) = 2 := map_ofNat _ 2
    change (PadicInt.Coe.ringHom (p := l)) 2 ^ n = 1 at this
    rw [e] at this
    simpa using this
  have hq' : (2 : ℚ) ^ n = 1 := by
    have := hq
    rw [← Rat.cast_zpow, ← Rat.cast_one] at this
    exact_mod_cast this
  exact (zpow_eq_one_iff_right₀ (by norm_num) (by norm_num)).mp hq'

theorem UpperTheory.V.U3.admissible_of_typeII :
    CohInp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : D.ULoc} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ {r : G ℚ Ω →* GG 3 (PadicAlgCl l)} (h : D.IsPt U g₁ r), ∀ (ι : Qbar l ≃+* ℂ),
      TypeII D.η r → (∀ W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l), D.IsExt r W → D.IsModular ι W) →
      Af.Adm2 ι e (N * (discr K).natAbs) (D.rhoK r h.mult) := by
  intro hC Ω _ _ _ K _ _ _ l hl c N _ e ψ D U g₁ hM r h ι hII hmod
  obtain ⟨h11, -, W, hext, hcont, hirr, -, hdet⟩ := typeII_facts hC D hM h hII
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hl1⟩ := dat_facts D
  let ψQ : G ℚ Ω →* (Qbar l)ˣ := (Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom).comp (Chr.dirG ℚ Ω ψ)
  have hΨ : ∀ g, D.ΨQ g = cycBar ℚ Ω l g ^ (e : ℤ) * ψQ g := fun g => by
    show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (chiO ℚ Ω l c.O g ^ (e : ℤ) * Chr.dirG ℚ Ω ψ g) = _
    rw [map_mul, map_zpow]
    rfl
  have hfin : ∀ g, ψQ g ^ Nat.card (ZMod N)ˣ = 1 := fun g => by
    show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (ψ.toUnitHom (Chr.cls ℚ Ω N g)) ^ _ = 1
    rw [← map_pow, ← map_pow, pow_card_eq_one', map_one, map_one]
  have hodd : Odd (discr K).natAbs := Nat.coprime_two_right.1 (D.gd.cop.coprime_dvd_right D.gd.N_even.two_dvd)
  have hkill : ∀ g : G ℚ Ω, (∀ ζ : Ω, ζ ^ (N * (discr K).natAbs) = 1 → g ζ = ζ) → ψQ g = 1 ∧ D.η g = 1 := fun g hg => by
    constructor
    · show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (ψ.toUnitHom (Chr.cls ℚ Ω N g)) = 1
      rw [cls_eq_one N g fun ζ hζ => hg ζ (by rw [pow_mul, hζ, one_pow]), map_one, map_one]
    · rw [← MonoidHom.mem_ker, D.η_ker]
      exact UpperTheory.mem_galOf_quadratic_of_fixes_discr_roots_of_unity Ω K D.gd.quad hodd g fun ζ hζ => hg ζ (by rw [pow_mul', hζ, one_pow])
  have hblk : ∀ g ∈ D.η.ker, (r g).mat = !![W g 0 0, 0, W g 0 1; 0, 1, 0; W g 1 0, 0, W g 1 1] := fun g hg =>
    block_form _ _ (hII.1 g hg) (h11 g hg) (hext.1 g hg)
  refine ⟨W, hirr, hmod W hext, ⟨hcont, fun w hw => ?_, fun w hw => ?_⟩, ?_, 1, fun s => ?_⟩
  · obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    have hAl : ¬ A.valuation (l : Ω) < 1 := fun h' => hw (((places ℚ Ω l A).2.2.1 w hA).1 h')
    obtain ⟨M, hMM⟩ := pt_inertia_away D hM h A hAl
    have h1 := UpperTheory.diagonal_on_subgroup_of_conjugate (Ine (F := ℚ) A ⊓ D.η.ker) W ψQ M fun g hg => by
      have hc : cycZ ℚ Ω l g = 1 := (places ℚ Ω l A).2.2.2 hAl hg.1
      have hc' : cycBar ℚ Ω l g = 1 := by
        rw [cycBar, MonoidHom.comp_apply, hc, map_one]
      rw [← hblk g hg.2, hMM g hg.1 hg.2, GG.mat, unitaryThreeReflection_left, tor_val, hΨ, hc', _root_.one_zpow, one_mul]
      congr 2
      funext i
      fin_cases i <;> simp [wt1]
    obtain ⟨χ, hχ, hd⟩ := UpperTheory.exists_isDiagOn_of_isDiagOn_inf_ker_sign _ _ W ψQ h1
    exact ⟨A, hA, χ, fun i s hs => hχ i s (hkill s hs).1 (hkill s hs).2, hd⟩
  · obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    have hAl : A.valuation (l : Ω) < 1 := ((places ℚ Ω l A).2.2.1 w hA).2 hw
    obtain ⟨-, M, hup, hdiag⟩ := pt_inertia_above hC D hM h A hAl
    obtain ⟨hIk, s₀, hs₀, hu⟩ := hl1 A hAl
    obtain ⟨hnorm, hID, -⟩ := Chr.decCyc Ω l A hl.out hAl
    have hs₀' : (D.ΨQ s₀ : Qbar l) ^ 2 ≠ 1 := by
      have := (hu.map (algebraMap c.O (PadicAlgCl l))).ne_zero
      rw [map_sub, map_pow, map_one, sub_ne_zero] at this
      exact this
    set v : Fin 3 → Qbar l := ((M⁻¹ : GL (Fin 3) (Qbar l)) : Matrix (Fin 3) (Fin 3) (Qbar l)) *ᵥ Pi.single 0 1 with hv
    have hv0 : v ≠ 0 := fun h0 => by
      have := congrArg (fun x => ((M : Matrix (Fin 3) (Fin 3) (Qbar l)) *ᵥ x) 0) (hv.symm.trans h0)
      simp only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, Matrix.mulVec_zero] at this
      simp at this
    have hev : ∀ s ∈ Ine (F := ℚ) A,
        !![W s 0 0, 0, W s 0 1; 0, 1, 0; W s 1 0, 0, W s 1 1] *ᵥ v = (D.ΨQ s : Qbar l) • v := fun s hs => by
      have hr : (r s).right = 1 := (h.mult s).trans (hIk hs)
      rw [← hblk s (hIk hs)]
      refine eigvec M _ _ ?_ fun i j hij => ?_
      · rw [← conj_mat M r s hr, hdiag s hs 0]
        simp [GG.mat, tor_val, wt1]
      · rw [← conj_mat M r s hr]
        exact hup s (hID hs) (hIk hs) i j hij
    have hv1 : v 1 = 0 := by
      have := congrFun (hev s₀ hs₀) 1
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at this
      by_contra hne
      have h3 : (D.ΨQ s₀ : Qbar l) = 1 := (mul_right_cancel₀ hne ((one_mul _).trans this)).symm
      exact hs₀' (by rw [h3, one_pow])
    obtain ⟨κ, hflag, hκ⟩ := UpperTheory.exists_isFlagOn_of_eigenvector_normal_subgroup (Dec (F := ℚ) A) (Ine (F := ℚ) A) W D.ΨQ ![v 0, v 2]
      (fun d hd s hs => hnorm.conj_mem' ⟨s, hID hs⟩ hs ⟨d, hd⟩)
      (fun h0 => hv0 (by
        funext i
        fin_cases i
        · exact congrFun h0 0
        · exact hv1
        · exact congrFun h0 1))
      (fun s hs => by
        have a0 := congrFun (hev s hs) 0
        have a2 := congrFun (hev s hs) 2
        funext i
        fin_cases i
        · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two] using a0
        · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two] using a2)
      (fun s hs => by rw [hdet, show D.η s = 1 from hIk hs]; simp)
      ⟨s₀, hs₀, hs₀'⟩
    have hκ' : ∀ i (s : ↥(Dec (F := ℚ) A)), (s : G ℚ Ω) ∈ Ine (F := ℚ) A →
        κ i s = cycBar ℚ Ω l s ^ (![(e : ℤ), -(e : ℤ)] i) * (![ψQ, ψQ⁻¹] i) s := fun i s hs => by
      fin_cases i
      · exact (hκ s hs).1.trans (hΨ s)
      · refine (hκ s hs).2.trans ?_
        rw [hΨ, mul_inv, ← _root_.zpow_neg]
        rfl
    refine ⟨A, hA, ![ψQ, ψQ⁻¹], κ, fun i s hs => ?_, hflag, hκ', Or.inl fun i j hij => ?_⟩
    · fin_cases i <;> simp [(hkill s hs).1]
    · obtain ⟨s, hs, hn⟩ := exists_two D.gd.l_odd A hAl
      have h1 := DFunLike.congr_fun hij ⟨s, hID hs⟩
      rw [MonoidHom.mul_apply, hκ' i _ hs, hκ' j _ hs] at h1
      have hf : ∀ i, ((![ψQ, ψQ⁻¹] i) s) ^ Nat.card (ZMod N)ˣ = 1 := fun i => by
        fin_cases i
        · exact hfin s
        · show (ψQ s)⁻¹ ^ _ = 1
          rw [inv_pow, hfin, inv_one]
      have h2 := congrArg (· ^ Nat.card (ZMod N)ˣ) h1
      simp only [mul_pow, hf, mul_one] at h2
      change (cycBar ℚ Ω l s ^ _) ^ _ = (cycBar ℚ Ω l s ^ _) ^ _ * cycBar ℚ Ω l s ^ _ at h2
      rw [← mul_pow, ← _root_.zpow_add_one, ← mul_inv_eq_one, ← inv_pow, ← mul_pow, ← _root_.zpow_sub, ← _root_.zpow_natCast,
        ← _root_.zpow_mul] at h2
      have h3 := (mul_eq_zero.1 (hn _ h2)).resolve_right (by exact_mod_cast Nat.card_pos.ne')
      fin_cases i <;> fin_cases j <;> simp at h3 <;> omega
  · refine ⟨N * (discr K).natAbs, Matrix.GeneralLinearGroup.det.comp W,
      Nat.mul_pos (NeZero.pos N) hodd.pos, fun s hs => Units.ext ?_, by simp⟩
    have := hdet s
    rw [(hkill s hs).2] at this
    simpa using this
  · rw [one_mul, inv_one, mul_one, D.rhoK_apply]
    exact hblk _ (D.η_ker ▸ galEmb_mem ℚ K Ω s)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsUnitPowNe
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem matIrr_ker {Γ κ Z : Type} [Group Γ] [Field κ] [IsAlgClosed κ] [CharZero κ] [CommGroup Z]
    (ρ : Γ →* GL (Fin 2) κ) (χ : Γ →* Z) (I : Subgroup Γ) (Ψ : Γ →* κˣ)
    (hsurj : ∀ g, ∃ s ∈ I, χ s = χ g)
    (htr : ∀ s ∈ I, (ρ s : Matrix (Fin 2) (Fin 2) κ).trace = (Ψ s : κ) + (Ψ s : κ)⁻¹)
    (hinf : ∃ u ∈ I, Ψ u ^ 8 ≠ 1)
    (hirr : MatIrr ⊤ fun g => (ρ g : Matrix (Fin 2) (Fin 2) κ)) :
    MatIrr χ.ker fun g => (ρ g : Matrix (Fin 2) (Fin 2) κ) := by
  by_contra hred
  obtain ⟨φ, h1, hker, h2, M, hM⟩ := exists_selfTwist ρ χ.ker (fun a b => by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [mul_comm (χ a) (χ b), mul_inv_cancel_right, mul_inv_cancel]) hirr hred
  obtain ⟨g, hg⟩ : ∃ g, φ g ≠ 1 := by
    by_contra hne
    push Not at hne
    exact h1 (MonoidHom.ext hne)
  obtain ⟨s, hs, hsg⟩ := hsurj g
  have hφs : φ s ≠ 1 := by
    intro h
    have : φ (s⁻¹ * g) = 1 := hker (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hsg, inv_mul_cancel])
    rw [map_mul, map_inv, h, inv_one, one_mul] at this
    exact hg this
  have key : ∀ t ∈ I, φ t ≠ 1 → Ψ t ^ 4 = 1 := by
    intro t ht hφ
    have e : (φ t : κ) • (ρ t : Matrix (Fin 2) (Fin 2) κ) =
        ((M⁻¹ : GL (Fin 2) κ) : Matrix (Fin 2) (Fin 2) κ) * (ρ t * M) := by
      rw [← hM t trivial, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    have e2 := congrArg Matrix.trace e
    rw [Matrix.trace_smul, Matrix.trace_mul_comm, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one,
      htr t ht, smul_eq_mul] at e2
    have e3 : (φ t : κ) - 1 ≠ 0 := fun h => hφ (Units.ext (sub_eq_zero.1 h))
    have e4 : (Ψ t : κ) + (Ψ t : κ)⁻¹ = 0 := by
      refine (mul_eq_zero.1 (?_ : ((φ t : κ) - 1) * _ = 0)).resolve_left e3
      rw [sub_mul, e2, one_mul, sub_self]
    have e5 : (Ψ t : κ) * (Ψ t : κ)⁻¹ = 1 := mul_inv_cancel₀ (Ψ t).ne_zero
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    linear_combination ((Ψ t : κ) ^ 3 - (Ψ t : κ)) * e4 - ((Ψ t : κ) ^ 2 - 1) * e5
  obtain ⟨u, hu, hu8⟩ := hinf
  have hu2 : φ (u ^ 2) = 1 := by
    rw [map_pow]
    exact DFunLike.congr_fun h2 u
  have h3 := key (s * u ^ 2) (mul_mem hs (pow_mem hu 2)) (by rwa [map_mul, hu2, mul_one])
  rw [map_mul, mul_pow, key s hs hφs, one_mul, map_pow, ← pow_mul] at h3
  exact hu8 h3

private theorem exists_unit_pow_ne (l : ℕ) [Fact l.Prime] : ∃ v : ℤ_[l]ˣ, ∀ n : ℕ, n ≠ 0 → v ^ n ≠ 1 := by
  have hu : IsUnit ((1 + l : ℕ) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    simp
  refine ⟨hu.unit, fun n hn h => ?_⟩
  have h2 := congrArg Units.val h
  rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_one] at h2
  have h3 : (1 + l) ^ n = 1 := by exact_mod_cast h2
  have := (Fact.out : l.Prime).pos
  rcases Nat.pow_eq_one.1 h3 with h4 | h4
  · omega
  · exact hn h4

theorem UpperTheory.V.U3.typeII_irr_cyc :
    CohInp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : D.ULoc} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ {r : G ℚ Ω →* GG 3 (PadicAlgCl l)} (h : D.IsPt U g₁ r),
      TypeII D.η r → ∀ W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l), D.IsExt r W →
        Af.IsIrr ((W.comp (galEmb ℚ K Ω)).comp (cycBar K Ω l).ker.subtype) := by
  intro hC Ω _ _ _ K _ _ _ l _ c N _ e ψ D U g₁ hM r h hII W hW
  obtain ⟨A, hA, -⟩ := dat_loc D
  have hIK : Ine (F := ℚ) A ≤ D.η.ker := ((dat_facts D).2.2.2.2.2.2.2.2.2.2 A hA).1
  have hch := (pt_inertia_above hC D hM h A hA).1
  have h11 := (typeII_facts hC D hM h hII).1
  have hmem : ∀ s, galEmb ℚ K Ω s ∈ D.η.ker := fun s => D.η_ker ▸ galEmb_mem ℚ K Ω s
  have hlift : ∀ g ∈ D.η.ker, ∃ s, galEmb ℚ K Ω s = g := fun g hg => by
    rw [D.η_ker, ← range_galEmb] at hg
    exact hg
  have hsur : ∀ v : ℤ_[l]ˣ, ∃ s : G K Ω, galEmb ℚ K Ω s ∈ Ine (F := ℚ) A ∧ cycZ K Ω l s = v := fun v => by
    obtain ⟨σ, hσ, hv⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA v
    obtain ⟨s, rfl⟩ := hlift σ (hIK hσ)
    exact ⟨s, hσ, hv⟩
  have main := matIrr_ker (W.comp (galEmb ℚ K Ω)) (cycBar K Ω l) ((Ine (F := ℚ) A).comap (galEmb ℚ K Ω))
    (D.ΨQ.comp (galEmb ℚ K Ω)) (fun g => ?_) (fun s hs => ?_) ?_ (fun X hX => ?_)
  · refine ⟨top_ne_bot, fun _ _ _ => trivial, fun X _ hX => main X fun g hg v hv => hX ⟨g, hg⟩ v hv⟩
  · obtain ⟨s, hs, hv⟩ := hsur (cycZ K Ω l g)
    refine ⟨s, hs, ?_⟩
    simp only [cycBar, MonoidHom.comp_apply, hv]
  · have h1 := Matrix.trace_eq_neg_charpoly_coeff (r (galEmb ℚ K Ω s)).mat
    rw [hch _ hs, ← Matrix.trace_eq_neg_charpoly_coeff] at h1
    rw [MonoidHom.comp_apply, hW.1 _ (hmem s), MonoidHom.comp_apply]
    have h2 := h11 _ (hmem s)
    have h3 : (corner (r (galEmb ℚ K Ω s)).mat).trace =
        (r (galEmb ℚ K Ω s)).mat 0 0 + (r (galEmb ℚ K Ω s)).mat 2 2 := Matrix.trace_fin_two _
    have h4 : (r0 D.η D.ΨQ (galEmb ℚ K Ω s)).mat.trace = (D.ΨQ (galEmb ℚ K Ω s) : PadicAlgCl l) + 1 +
        (D.ΨQ (galEmb ℚ K Ω s) : PadicAlgCl l)⁻¹ := by
      simp [GG.mat, tor_val, wt1, Fin.sum_univ_three]
    rw [Matrix.trace_fin_three, h4, h2] at h1
    rw [h3]
    linear_combination h1
  · obtain ⟨v, hv⟩ := exists_unit_pow_ne l
    obtain ⟨s, hs, hsv⟩ := hsur v
    refine ⟨s, hs, fun h8 => ?_⟩
    have ho : orderOf ψ ≠ 0 := fun h0 => D.gd.ord (h0 ▸ dvd_zero l)
    have he : e ≠ 0 := Nat.one_le_iff_ne_zero.1 D.gd.e_pos
    have h1 : D.Ψ (galEmb ℚ K Ω s) ^ 8 = 1 := by
      apply Units.ext
      apply Subtype.val_injective
      have := congrArg Units.val h8
      exact this
    have h2 : Chr.dirG ℚ Ω ψ (galEmb ℚ K Ω s) ^ orderOf ψ = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Chr.dirG, MonoidHom.comp_apply, MulChar.coe_toUnitHom,
        ← MulChar.pow_apply_coe, pow_orderOf_eq_one, MulChar.one_apply_coe, Units.val_one]
    have h3 : D.Ψ (galEmb ℚ K Ω s) = Units.map (algebraMap ℤ_[l] c.O).toMonoidHom v ^ e *
        Chr.dirG ℚ Ω ψ (galEmb ℚ K Ω s) := by
      rw [← hsv, ← zpow_natCast]
      rfl
    have h4 : Units.map (algebraMap ℤ_[l] c.O).toMonoidHom (v ^ (e * (8 * orderOf ψ))) = 1 := by
      have := congrArg (· ^ orderOf ψ) h1
      simp only [one_pow] at this
      rw [← pow_mul, h3, mul_pow, mul_comm 8, pow_mul (Chr.dirG ℚ Ω ψ _), h2, one_pow, mul_one,
        ← pow_mul, mul_comm _ 8] at this
      rw [map_pow, this]
    refine hv (e * (8 * orderOf ψ)) (mul_ne_zero he (mul_ne_zero (by norm_num) ho)) ?_
    have hinj : Function.Injective (algebraMap ℤ_[l] c.O) := fun x y hxy => by
      have : algebraMap ℤ_[l] (PadicAlgCl l) x = algebraMap ℤ_[l] (PadicAlgCl l) y := congrArg Subtype.val hxy
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l) y] at this
      exact Subtype.val_injective ((algebraMap ℚ_[l] (PadicAlgCl l)).injective this)
    exact (Units.map_injective (f := (algebraMap ℤ_[l] c.O).toMonoidHom) hinj) (h4.trans (map_one _).symm)
  · refine hII.2 X fun g hg v hv => ?_
    obtain ⟨s, rfl⟩ := hlift g hg
    have := hX s trivial v hv
    simp only [MonoidHom.comp_apply, hW.1 _ hg] at this
    exact this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.LiftingTheory
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem left_conj {R : Type} [CommRing R] {m : ℕ} (x y : GG m R) (h1 : x.mat = 1) (h2 : x.right = -1)
    (h3 : y.right = 1) : (x * y * x⁻¹).left = theta y.left := by
  have hl : x.left = 1 := Units.ext h1
  simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, SemidirectProduct.inv_left,
    hl, h2, h3, inv_one, mul_one, one_mul, sgnAct_neg_one, map_one]

private theorem pairing_theta {R : Type} [CommRing R] {m : ℕ} (a : GL (Fin m) R) :
    (a : Matrix (Fin m) (Fin m) R)ᵀ * Jmat R m * (theta a : GL (Fin m) R) = Jmat R m := by
  rw [theta_val, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ (Jmat R m) (Jmat R m), Jmat_mul_Jmat,
    Matrix.mul_one, ← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one,
    Matrix.one_mul]

private theorem cont_hom {Γ M : Type} [Group Γ] [TopologicalSpace Γ] [ContinuousInv Γ] [Monoid M] [TopologicalSpace M]
    (f : Γ →* Mˣ) (h : Continuous fun g => (f g : M)) : Continuous f := by
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  simp only [← map_inv]
  exact h.comp continuous_inv

private theorem irr_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (ρ : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) :
    (Af.tw ρ χ⁻¹).comp χ.ker.subtype = ρ.comp χ.ker.subtype := by
  refine MonoidHom.ext fun s => Units.ext ?_
  have hs : χ s = 1 := s.2
  show (Af.tw ρ χ⁻¹ s : Matrix (Fin n) (Fin n) k) = ρ s
  rw [Af.tw_val, MonoidHom.inv_apply, hs, inv_one, Units.val_one, one_smul]

private theorem ad_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (ρ : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) (s : Γ)
    (X : Matrix (Fin n) (Fin n) k) :
    (Af.tw ρ χ s : Matrix (Fin n) (Fin n) k) * X * ((Af.tw ρ χ s)⁻¹ : GL (Fin n) k) =
      (ρ s : Matrix (Fin n) (Fin n) k) * X * ((ρ s)⁻¹ : GL (Fin n) k) := by
  rw [← map_inv, ← map_inv, Af.tw_val, Af.tw_val, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, one_smul]

theorem UpperTheory.V.U3.bloch_kato_type_one :
    CohInp → Af.AdVanishK → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : D.ULoc} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ {r : G ℚ Ω →* GG 3 (PadicAlgCl l)} (h : D.IsPt U g₁ r), ∀ [IsCMField K] (ι : Qbar l ≃+* ℂ),
      TypeI D.η r → D.IsAutI ι r h.mult → Af.BlochKatoSelmerVanishes l (adRep r) := by
  intro hC hA Ω _ _ _ K _ _ _ l _ c N _ e ψ D U g₁ hM r h _ ι hI hAut
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : IsAlgClosure K Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  have hK : ∀ s : G K Ω, (r (galEmb ℚ K Ω s)).right = 1 := fun s =>
    (h.mult _).trans (show galEmb ℚ K Ω s ∈ D.η.ker from D.η_ker ▸ galEmb_mem ℚ K Ω s)
  have hc : (r D.cc).right = -1 := (h.mult _).trans hM.ηc
  have hz : Continuous fun s : G K Ω => ((cycZ K Ω l s : ℤ_[l]ˣ) : ℤ_[l]) :=
    Units.continuous_val.comp (continuous_cycZ K Ω l)
  have hcyc : Continuous fun s : G K Ω => (cycBar K Ω l s : Qbar l) :=
    (continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp
      (continuous_subtype_val.comp hz)
  refine hA K D.gd.quad 3 (by norm_num) l Ω ι _ ?_ hAut ?_ _ ⟨D.cc, Jgl _ 3, D.conj, ?_, ?_, ?_⟩
  · refine cont_hom _ ?_
    simp only [Af.tw_val, MonoidHom.inv_apply, ← map_inv]
    exact (hcyc.comp continuous_inv).smul (h.cont.comp (galEmbTop ℚ K Ω).1.continuous)
  · rw [irr_tw]
    exact typeI_irr_cyc hC D hM h hI
  · intro s s' hs
    have hs' : galEmb ℚ K Ω s' = D.cc * galEmb ℚ K Ω s * D.cc⁻¹ := hs
    have h1 : cycBar K Ω l s' = cycBar K Ω l s := by
      show cycBar ℚ Ω l (galEmb ℚ K Ω s') = cycBar ℚ Ω l (galEmb ℚ K Ω s)
      rw [hs', map_mul, map_mul, map_inv, mul_inv_cancel_comm]
    have h2 : D.rhoK r h.mult s' = theta (D.rhoK r h.mult s) := by
      rw [D.rhoK_apply, D.rhoK_apply, hs', map_mul, map_mul, map_inv]
      exact left_conj _ _ h.norm.atc hc (hK s)
    rw [Af.tw_val, Af.tw_val, h2, MonoidHom.inv_apply, MonoidHom.inv_apply, h1, Matrix.transpose_smul,
      Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Units.val_mul]
    have h3 : (cycBar K Ω l ^ (1 - ((3 : ℕ) : ℤ))) s = (cycBar K Ω l s)⁻¹ * (cycBar K Ω l s)⁻¹ := by
      rw [MonoidHom.zpow_apply, show (1 - ((3 : ℕ) : ℤ)) = -1 + -1 by norm_num, _root_.zpow_add, _root_.zpow_neg_one]
    rw [h3]
    exact congrArg _ (pairing_theta _)
  · intro s X
    rw [ad_tw]
    show (r (galEmb ℚ K Ω s)).adFun X = _
    rw [GG.adFun, if_pos (hK s)]
    rfl
  · intro X
    have hl : (r D.cc).left = 1 := Units.ext h.norm.atc
    show (r D.cc).adFun X = _
    rw [GG.adFun, hc, if_neg (by decide), h.norm.atc, hl, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]
    rfl
end

