import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PosExact
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0013
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0009
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0022
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0018
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KisinCrTrivial
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CrUnipChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmBilin
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0019

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsCrystallineTriangularLiftOfMemFiniteCocycl
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

private theorem mem_ker_smul {B E : Type} [CommRing B] [CommRing E] (π : B →+* E) (u v : B) (hu : π u = 0)
    (hv : π v = 0) : ((u, v) : B × B) ∈ (RingHom.ker π) • (⊤ : Submodule B (B × B)) := by
  have h : ((u, v) : B × B) = u • ((1, 0) : B × B) + v • ((0, 1) : B × B) := by simp
  rw [h]
  exact Submodule.add_mem _ (Submodule.smul_mem_smul hu trivial) (Submodule.smul_mem_smul hv trivial)

private def triHom {G B : Type} [Group G] [CommRing B] (κ : Fin 3 → G →* Bˣ) (x y z : G → B)
    (hx : ∀ g h, x (g * h) = x g + ((κ 0 / κ 1) g : Bˣ) * x h)
    (hy : ∀ g h, y (g * h) = y g + ((κ 1 / κ 2) g : Bˣ) * y h)
    (hz : ∀ g h, z (g * h) = z g + (((κ 0 / κ 2) g : Bˣ) * z h + x g * ((κ 1 / κ 2) g : Bˣ) * y h)) :
    G →* Matrix (Fin 3) (Fin 3) B where
  toFun g := triM (fun i => κ i g) (x g) (y g) (z g)
  map_one' := by
    have h1 := hx 1 1
    have h2 := hy 1 1
    have h3 := hz 1 1
    simp only [mul_one, map_one, Units.val_one, one_mul, left_eq_add] at h1 h2
    simp only [mul_one, map_one, Units.val_one, one_mul, left_eq_add, h1, zero_mul, add_zero] at h3
    ext i j
    fin_cases i <;> fin_cases j <;> simp [triM, h1, h2, h3]
  map_mul' g h := by
    have e : ∀ i j, (κ i g : B) = (((κ i / κ j) g : Bˣ) : B) * κ j g := fun i j => by
      rw [← Units.val_mul, MonoidHom.div_apply, div_mul_cancel]
    have e1 := e 0 1
    have e2 := e 1 2
    have e3 := e 0 2
    have h1 := hx g h
    have h2 := hy g h
    have h3 := hz g h
    generalize (((κ 0 / κ 1) g : Bˣ) : B) = p at *
    generalize (((κ 1 / κ 2) g : Bˣ) : B) = q at *
    generalize (((κ 0 / κ 2) g : Bˣ) : B) = r at *
    ext i j
    fin_cases i <;> fin_cases j <;> simp [triM, h1, h2, h3, Matrix.mul_apply, Fin.sum_univ_three]
    · linear_combination (-(x h * κ 1 h)) * e1
    · linear_combination (-(z h * κ 2 h)) * e3 - (x g * y h * κ 2 h) * e2
    · linear_combination (-(y h * κ 2 h)) * e2

theorem UpperTheory.exists_crystalline_triangular_lift_of_mem_finiteCocycles :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) {e : ℕ} {ψ : G →* Eˣ} {κ : Fin 3 → G →* Bˣ}, Chars φ π e ψ κ → ∀ x ∈ UpperTheory.V.Loc.finiteCocycles φ (chRep (κ 0 / κ 1)), ∀ y ∈ UpperTheory.V.Loc.finiteCocycles φ (chRep (κ 1 / κ 2)), (∀ g, π (x g) = 0) → ∃ (z : G → B) (ρ : G →* GL (Fin 3) B), Continuous z ∧ (∀ g, (ρ g : Matrix (Fin 3) (Fin 3) B) = triM (fun i => κ i g) (x g) (y g) (z g)) ∧ IsCr φ (colRep ρ) := by
  intro hP l _ G _ _ _ φ hφ E _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ e ψ κ hκ x hx y hy hx0
  haveI : ContinuousConstSMul E B := contConstSMul_alg E
  haveI : Module.Finite E B := Module.Finite.of_restrictScalars_finite ℚ_[l] E B
  have hxc : Continuous x := hx.1.1
  have hyc : Continuous y := hy.1.1
  have hxm : ∀ g h, x (g * h) = x g + ((κ 0 / κ 1) g : Bˣ) * x h := hx.1.2
  have hym : ∀ g h, y (g * h) = y g + ((κ 1 / κ 2) g : Bˣ) * y h := hy.1.2
  have hab : (κ 0 / κ 2) / (κ 1 / κ 2) = κ 0 / κ 1 := div_div_div_cancel_right _ _ _
  have hxm' : ∀ g h, x (g * h) = x g + (((κ 0 / κ 2) / (κ 1 / κ 2)) g : Bˣ) * x h := by rw [hab]; exact hxm
  have hcr : ∀ i, IsCr φ (chRep (κ i)) := fun i =>
    crUnr φ hφ _ (contAction_chRep (hκ.cont i)) (e * wt1 i) fun g hg v => by
      rw [chRep_apply, hκ.ine g hg, smul_eq_mul]
  have hcd : ∀ i j, Continuous fun g => (((κ i / κ j) g : Bˣ) : B) := fun i j => cont_char_div (hκ.cont i) (hκ.cont j)
  have hcr' : ∀ i j, IsCr φ (chRep (κ i / κ j)) := fun i j =>
    crUnr φ hφ _ (contAction_chRep (hcd i j)) (e * wt1 i - e * wt1 j) fun g hg v => by
      rw [chRep_apply, MonoidHom.div_apply, hκ.ine g hg, hκ.ine g hg, smul_eq_mul, zpow_sub, div_eq_mul_inv]
  have hred : ∀ i j g, π (((κ i / κ j) g : Bˣ) : B) = ((ψ g ^ (wt1 i - wt1 j) : Eˣ) : E) := fun i j g => by
    have h1 : (((κ i / κ j) g : Bˣ) : B) * κ j g = κ i g := by
      rw [← Units.val_mul, MonoidHom.div_apply, div_mul_cancel]
    have h2 := congrArg π h1
    rw [map_mul, hκ.red, hκ.red] at h2
    rw [zpow_sub, Units.val_mul, ← h2, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  let T := ext2 (κ 0 / κ 2) (κ 1 / κ 2) x hxm'
  have hTc : ContAction T := contAction_charExtension_of_continuous_cocycle (hcd 0 2) (hcd 1 2) hxm' hxc
  have hTcr : IsCr φ T :=
    (UpperTheory.isCrystalline_extension_iff_mem_finiteCocycles φ hφ _ _ (hcd 0 2) (hcd 1 2) x hxm' hxc (hcr' 0 2) (hcr' 1 2)).2 (by rw [hab]; exact hx)
  have hTdr : IsDr φ (resCoef E T) := (isCrys_isDR_restrict_openSubgroup φ hφ T hTc).1 hTcr
  have hwt : ∀ n : ℕ, 1 ≤ n → ψ ^ n ∈ {κ : G →* Eˣ | ∃ w : ℤ, 1 ≤ w ∧ HasWeight φ κ w} := fun n hn =>
    ⟨((e * n : ℕ) : ℤ), by exact_mod_cast Nat.mul_pos hκ.e_pos hn, ⊤, by simp, fun g _ hg => by
      rw [MonoidHom.pow_apply, hκ.wt g hg, zpow_natCast, pow_mul]⟩
  have hTf : FiltBy (resCoef E T) {κ | ∃ w : ℤ, 1 ≤ w ∧ HasWeight φ κ w} := by
    refine UpperTheory.filtBy_restrictScalars_of_residual_characters π hπ T _ (ι := Fin 2) ![(1, 0), (0, 1)] ![ψ ^ 2, ψ ^ 1] ?_ ?_ ?_
    · rw [eq_top_iff]
      rintro ⟨u, v⟩ -
      have h : ((u, v) : B × B) = u • ((1, 0) : B × B) + v • ((0, 1) : B × B) := by simp
      rw [h]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
    · intro j
      fin_cases j
      · exact hwt 2 (by norm_num)
      · exact hwt 1 le_rfl
    · intro g j
      have a1 := hred 0 2 g
      have a2 := hred 1 2 g
      have w1 : wt1 0 - wt1 2 = ((2 : ℕ) : ℤ) := by decide
      have w2 : wt1 1 - wt1 2 = ((1 : ℕ) : ℤ) := by decide
      rw [w1, zpow_natCast] at a1
      rw [w2, zpow_natCast] at a2
      fin_cases j
      · refine mem_ker_smul (π : B →+* E) _ _ ?_ ?_
        · change π (((κ 0 / κ 2) g : Bˣ) * 1 + x g * ((κ 1 / κ 2) g : Bˣ) * 0 - ((ψ g ^ 2 : Eˣ) : E) • (1 : B)) = 0
          rw [mul_one, mul_zero, add_zero, map_sub, a1, map_smul, map_one, smul_eq_mul, mul_one, sub_self]
        · change π (((κ 1 / κ 2) g : Bˣ) * 0 - ((ψ g ^ 2 : Eˣ) : E) • (0 : B)) = 0
          rw [mul_zero, smul_zero, sub_zero, map_zero]
      · refine mem_ker_smul (π : B →+* E) _ _ ?_ ?_
        · change π (((κ 0 / κ 2) g : Bˣ) * 0 + x g * ((κ 1 / κ 2) g : Bˣ) * 1 - ((ψ g ^ 1 : Eˣ) : E) • (0 : B)) = 0
          rw [mul_one, mul_zero, zero_add, smul_zero, sub_zero, map_mul, hx0, zero_mul]
        · change π (((κ 1 / κ 2) g : Bˣ) * 1 - ((ψ g ^ 1 : Eˣ) : E) • (1 : B)) = 0
          rw [mul_one, map_sub, a2, map_smul, map_one, smul_eq_mul, mul_one, sub_self]
  obtain ⟨c, hc, hcy⟩ := (posExact hP φ hφ (resCoef E T) (resCoef E (chRep (κ 1 / κ 2))) hTc
    (contAction_chRep (hcd 1 2)) ⟨hTdr, hTf⟩ (LinearMap.snd E B B) (fun g v => rfl)).1 Prod.snd_surjective y hy
  have hcT : c ∈ UpperTheory.V.Loc.finiteCocycles φ T := hc
  have hc2 : ∀ g, (c g).2 = y g := fun g => congrFun hcy g
  have hzc : Continuous fun g => (c g).1 := hcT.1.1.fst
  have hzm : ∀ g h, (c (g * h)).1 =
      (c g).1 + (((κ 0 / κ 2) g : Bˣ) * (c h).1 + x g * ((κ 1 / κ 2) g : Bˣ) * y h) := fun g h => by
    rw [← hc2 h]
    exact congrArg Prod.fst (hcT.1.2 g h)
  let ρ := (triHom κ x y (fun g => (c g).1) hxm hym hzm).toHomUnits
  refine ⟨fun g => (c g).1, ρ, hzc, fun g => rfl, ?_⟩
  have h01 : IsCr φ (ext2 (κ 0) (κ 1) x hxm) :=
    (UpperTheory.isCrystalline_extension_iff_mem_finiteCocycles φ hφ _ _ (hκ.cont 0) (hκ.cont 1) x hxm hxc (hcr 0) (hcr 1)).2 hx
  refine (UpperTheory.isCrystalline_upperTriangular_iff_mem_finiteCocycles φ hφ κ hκ.cont x y _ ρ hxc hyc hzc (fun g => rfl) hxm h01 (hcr 2)).2 ?_
  have hT : twist (κ 2)⁻¹ (ext2 (κ 0) (κ 1) x hxm) = T := by
    refine MonoidHom.ext fun g => LinearMap.ext fun v => ?_
    rw [twist_apply, characterExtensionRep_apply, characterExtensionRep_apply]
    simp only [div_eq_mul_inv, MonoidHom.mul_apply, Units.val_mul, Prod.smul_mk, smul_eq_mul]
    ext <;> simp only [] <;> ring
  have hc' : (fun g => ((c g).1, y g)) = c := funext fun g => by rw [← hc2 g]
  rw [hT, hc']
  exact hcT
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TorsionDatumFiniteCocyclesBaseChange
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

private theorem multiplicity_one_positive {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {η : GQ l →* ℤˣ} {Ψ : GQ l →* Eˣ} {H : Subgroup (GQ l)} {e : ℕ}
    (hD : TriDat η Ψ H e) {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B]
    [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E)
    (hπ : ∀ a, π a = 0 → IsNilpotent a) (T : Tor η B) (hT : T.Good π Ψ) :
    Positive (MonoidHom.id (GQ l)) (resCoef E T.M1) := by
  haveI : ContinuousConstSMul E B := contConstSMul_alg E
  haveI : Module.Finite E B := Module.Finite.of_restrictScalars_finite ℚ_[l] E B
  have hc : ContAction (resCoef E T.M1) := T.contAction_torus_module hD.ηlc hT.cont hT.cont_inv
  have w0 : wt1 (0 : Fin 3) = 1 := by decide
  have w1 : wt1 (1 : Fin 3) = 0 := by decide
  have w2 : wt1 (2 : Fin 3) = -1 := by decide
  have hid : IsOpenEmbedding (MonoidHom.id (GQ l)) := IsOpenEmbedding.id
  refine ⟨?_, ?_⟩
  · have hφ : IsOpenEmbedding ((MonoidHom.id (GQ l)).comp H.subtype) := hD.isOpen.isOpenEmbedding_subtypeVal
    have hcH : ContAction ((resCoef E T.M1).comp H.subtype : Representation E H (B × B)) :=
      Continuous.comp (g := fun p : GQ l × B × B => resCoef E T.M1 p.1 p.2)
        (f := fun p : H × B × B => ((p.1 : GQ l), p.2)) hc (by fun_prop)
    rw [((isCrys_isDR_restrict_openSubgroup _ hid _ hc).2 H hD.isOpen).2]
    refine (isCrys_isDR_restrict_openSubgroup _ hφ _ hcH).1 (crUnr _ hφ _ hcH e fun g hg x => ?_)
    have hg' : (g : GQ l) ∈ Iq l := hg
    have hu : ∀ i, T.t g i = Units.map (algebraMap E B : E →* B) (Ψ g ^ wt1 i) := fun i =>
      Units.ext (hT.ine g hg' i)
    change T.M1 g x = ((cycA l l E g ^ (e : ℤ) : Eˣ) : E) • x
    rw [zpow_natCast, ← hD.ΨH g g.2 hg', Tor.adjointSuperdiagRep_apply, if_pos (hD.ηH g g.2)]
    simp only [hu, w0, w1, w2, ← map_div]
    ext <;> simp [Algebra.smul_def]
  · let ε : GQ l →* Eˣ := (Units.map (Int.castRingHom E : ℤ →* E)).comp η
    have h2 : (2 : B) * algebraMap ℚ_[l] B (1 / 2) = 1 := by
      rw [← map_ofNat (algebraMap ℚ_[l] B) 2, ← map_mul]
      norm_num
    refine UpperTheory.filtBy_restrictScalars_of_residual_characters π hπ T.M1 _ ![((1 : B), (1 : B)), (1, -1)] ![ε * Ψ, Ψ] ?_ ?_ ?_
    · rw [eq_top_iff]
      rintro ⟨a, b⟩ -
      have : (a, b) = (algebraMap ℚ_[l] B (1 / 2) * (a + b)) • ((1 : B), (1 : B)) +
          (algebraMap ℚ_[l] B (1 / 2) * (a - b)) • ((1 : B), (-1 : B)) := by
        ext
        · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
          linear_combination (-a) * h2
        · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
          linear_combination (-b) * h2
      rw [this]
      exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
    · have he : (1 : ℤ) ≤ e := by exact_mod_cast hD.e_pos
      intro j
      refine ⟨e, he, H, hD.isOpen, fun g hg hI => ?_⟩
      have h1 := hD.ΨH g hg hI
      fin_cases j
      · simp [ε, hD.ηH g hg, h1]
      · simp [h1]
    · have key : ∀ v : B × B, π v.1 = 0 → π v.2 = 0 →
          v ∈ (RingHom.ker (π : B →+* E)) • (⊤ : Submodule B (B × B)) := by
        rintro ⟨a, b⟩ ha hb
        have : (a, b) = a • ((1 : B), (0 : B)) + b • ((0 : B), (1 : B)) := by simp
        rw [this]
        exact add_mem (Submodule.smul_mem_smul ha trivial) (Submodule.smul_mem_smul hb trivial)
      intro g j
      have hu : ∀ i, Units.map (π : B →* E) (T.t g i) = Ψ g ^ wt1 i := fun i => Units.ext (hT.red g i)
      have ha : π ((T.t g 0 / T.t g 1 : Bˣ) : B) = Ψ g := by
        have : Units.map (π : B →* E) (T.t g 0 / T.t g 1) = Ψ g := by simp [map_div, hu, w0, w1]
        exact congrArg Units.val this
      have hb : π ((T.t g 1 / T.t g 2 : Bˣ) : B) = Ψ g := by
        have : Units.map (π : B →* E) (T.t g 1 / T.t g 2) = Ψ g := by simp [map_div, hu, w1, w2]
        exact congrArg Units.val this
      have hn : ((-1 : ℤˣ) = 1) = False := by decide
      rw [Tor.adjointSuperdiagRep_apply]
      generalize ((T.t g 0 / T.t g 1 : Bˣ) : B) = a at ha ⊢
      generalize ((T.t g 1 / T.t g 2 : Bˣ) : B) = b at hb ⊢
      apply key <;> rcases Int.units_eq_one_or (η g) with hg | hg <;> fin_cases j <;>
        simp [ε, hg, hn, ha, hb, Algebra.smul_def]

theorem UpperTheory.torsionDatum_finiteCocycles_baseChange :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {η : GQ l →* ℤˣ} {Ψ : GQ l →* Eˣ} {H : Subgroup (GQ l)} {e : ℕ} (hD : TriDat η Ψ H e) {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) {B' : Type} [CommRing B'] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B'] [TopologicalSpace B'] [IsModuleTopology ℚ_[l] B'] [IsTopologicalRing B'] [Algebra ℤ_[l] B'] [IsScalarTower ℤ_[l] ℚ_[l] B'] [Algebra E B'] [IsScalarTower ℚ_[l] E B'] (π' : B' →ₐ[E] E) (hπ' : ∀ a, π' a = 0 → IsNilpotent a) (p : B →ₐ[E] B'), Function.Surjective p → ∀ (T : Tor η B) (T' : Tor η B'), T.Good π Ψ → T'.Good π' Ψ → (∀ g i, p (T.t g i : B) = (T'.t g i : B')) → ∀ β' ∈ UpperTheory.V.Loc.finiteCocycles (MonoidHom.id (GQ l)) T'.M1, ∃ β ∈ UpperTheory.V.Loc.finiteCocycles (MonoidHom.id (GQ l)) T.M1, ∀ g, p (β g).1 = (β' g).1 ∧ p (β g).2 = (β' g).2 := by
  intro hP l _ E _ _ _ _ _ η Ψ H e hD B _ _ _ _ _ _ _ _ _ _ π hπ B' _ _ _ _ _ _ _ _ _ _ π' _ p hp T T' hT hT' ht β' hβ'
  haveI : ContinuousConstSMul E B := contConstSMul_alg E
  haveI : ContinuousConstSMul E B' := contConstSMul_alg E
  have hc : ContAction (resCoef E T.M1) := T.contAction_torus_module hD.ηlc hT.cont hT.cont_inv
  have hc' : ContAction (resCoef E T'.M1) := T'.contAction_torus_module hD.ηlc hT'.cont hT'.cont_inv
  have hu : ∀ g i j, p ((T.t g i / T.t g j : Bˣ) : B) = ((T'.t g i / T'.t g j : B'ˣ) : B') := fun g i j => by
    have h : ∀ i, Units.map (p : B →* B') (T.t g i) = T'.t g i := fun i => Units.ext (ht g i)
    rw [← h, ← h, ← map_div]
    rfl
  obtain ⟨β, hβ, hpβ⟩ := (posExact hP (MonoidHom.id (GQ l)) IsOpenEmbedding.id (resCoef E T.M1) (resCoef E T'.M1)
    hc hc' (multiplicity_one_positive hD π hπ T hT) (p.toLinearMap.prodMap p.toLinearMap) (fun g x => by
      change Prod.map p p (T.M1 g x) = T'.M1 g (Prod.map p p x)
      simp only [Tor.adjointSuperdiagRep_apply]
      split_ifs <;> simp only [Prod.map, map_mul, map_neg, hu])).1 (hp.prodMap hp) β'
    ((z1fMap (MonoidHom.id (GQ l)) T'.M1 (resCoef E T'.M1)).2 LinearMap.id (fun _ _ => rfl) β' hβ')
  refine ⟨β, (z1fMap (MonoidHom.id (GQ l)) (resCoef E T.M1) T.M1).2 LinearMap.id (fun _ _ => rfl) β hβ, fun g => ?_⟩
  rw [← hpβ]
  exact ⟨rfl, rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TorsionDatumFiniteCocyclesCompare
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

theorem UpperTheory.torsionDatum_finiteCocycles_compare :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {η : GQ l →* ℤˣ} {Ψ : GQ l →* Eˣ} {H : Subgroup (GQ l)} {e : ℕ} (hD : TriDat η Ψ H e) {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) {B' : Type} [CommRing B'] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B'] [TopologicalSpace B'] [IsModuleTopology ℚ_[l] B'] [IsTopologicalRing B'] [Algebra ℤ_[l] B'] [IsScalarTower ℤ_[l] ℚ_[l] B'] [Algebra E B'] [IsScalarTower ℚ_[l] E B'] (π' : B' →ₐ[E] E) (hπ' : ∀ a, π' a = 0 → IsNilpotent a) (p : B →ₐ[E] B'), Function.Surjective p → ∀ (T : Tor η B) (T' : Tor η B'), T.Good π Ψ → T'.Good π' Ψ → (∀ g i, p (T.t g i : B) = (T'.t g i : B')) → ∀ δ' ∈ UpperTheory.V.Loc.finiteCocycles (MonoidHom.id (GQ l)) (chRep T'.χ2), ∃ δ ∈ UpperTheory.V.Loc.finiteCocycles (MonoidHom.id (GQ l)) (chRep T.χ2), ∀ g, p (δ g) = δ' g := by
  intro hP l _ E _ _ _ _ _ η Ψ H e hD B _ _ _ _ _ _ _ _ _ _ π hπ B' _ _ _ _ _ _ _ _ _ _ π' hπ' p hp T T' hT hT'
    hTT δ' hδ'
  haveI : ContinuousConstSMul E B := contConstSMul_alg E
  haveI : ContinuousConstSMul E B' := contConstSMul_alg E
  haveI : Module.Finite E B := Module.Finite.of_restrictScalars_finite ℚ_[l] E B
  have hc : ContAction (chRep T.χ2) := contAction_chRep (T.continuous_χ2 hD.ηlc hT.cont hT.cont_inv)
  have hc' : ContAction (chRep T'.χ2) := contAction_chRep (T'.continuous_χ2 hD.ηlc hT'.cont hT'.cont_inv)
  have hcE : ContAction (resCoef E (chRep T.χ2)) := hc
  have hcE' : ContAction (resCoef E (chRep T'.χ2)) := hc'
  have hid : IsOpenEmbedding (MonoidHom.id (GQ l)) := IsOpenEmbedding.id
  have hI : ∀ g ∈ H, g ∈ Iq l →
      T.χ2 g = Units.map (algebraMap E B : E →* B) (cycA l l E g ^ ((2 * e : ℕ) : ℤ)) := by
    intro g hg hgI
    have h := (hT.chars hD).ine ⟨g, hg⟩ hgI
    simp only [Tor.ch_apply, Subgroup.coe_subtype] at h
    change Units.map _ (η g) * (T.t g 0 / T.t g 2) = _
    rw [hD.ηH g hg, map_one, one_mul, h 0, h 2, map_zpow, algebraMap_cycA, div_eq_mul_inv, ← zpow_sub]
    congr 1
    simp [wt1]
    ring
  have hpos : Positive (MonoidHom.id (GQ l)) (resCoef E (chRep T.χ2)) := by
    refine ⟨?_, ?_⟩
    · refine (((isCrys_isDR_restrict_openSubgroup _ hid _ hcE).2 H hD.isOpen).2).2 ?_
      have hH : IsOpenEmbedding ((MonoidHom.id (GQ l)).comp H.subtype) := hD.isOpen.isOpenEmbedding_subtypeVal
      have hcH : ContAction ((resCoef E (chRep T.χ2)).comp H.subtype : Representation E H B) :=
        (((T.continuous_χ2 hD.ηlc hT.cont hT.cont_inv).comp continuous_subtype_val).comp continuous_fst).mul
          continuous_snd
      refine (isCrys_isDR_restrict_openSubgroup _ hH _ hcH).1 (crUnr _ hH _ hcH ((2 * e : ℕ) : ℤ) fun g hg x => ?_)
      change (T.χ2 g : B) * x = _
      rw [hI g g.2 hg, Algebra.smul_def]
      rfl
    · refine UpperTheory.filtBy_restrictScalars_of_residual_characters π hπ _ _ (fun _ : Unit => (1 : B))
        (fun _ => (Units.map (π : B →* E)).comp T.χ2) ?_ (fun _ => ?_) (fun g _ => ?_)
      · simp [Ideal.span_singleton_one]
      · refine ⟨((2 * e : ℕ) : ℤ), by have := hD.e_pos; omega, H, hD.isOpen, fun g hg hgI => ?_⟩
        apply Units.ext
        change π (T.χ2 g : B) = _
        rw [hI g hg hgI]
        exact π.commutes _
      · rw [Ideal.smul_eq_mul, Ideal.mul_top, RingHom.mem_ker]
        change π ((T.χ2 g : B) * 1 - π (T.χ2 g : B) • (1 : B)) = 0
        simp
  have hχ : ∀ g, p (T.χ2 g : B) = (T'.χ2 g : B') := by
    intro g
    have h : ∀ i, Units.map (p : B →* B') (T.t g i) = T'.t g i := fun i => Units.ext (hTT g i)
    rw [Tor.χ2_apply, Tor.χ2_apply, map_mul, map_intCast, ← h 0, ← h 2, ← map_div]
    rfl
  obtain ⟨δ, hδ, hδp⟩ := (posExact hP _ hid _ _ hcE hcE' hpos p.toLinearMap (fun g x => by
      change p ((T.χ2 g : B) * x) = (T'.χ2 g : B') * p x
      rw [map_mul, hχ])).1 hp δ'
    ((z1fMap (MonoidHom.id (GQ l)) (chRep T'.χ2) (resCoef E (chRep T'.χ2))).2 LinearMap.id (fun _ _ => rfl) δ' hδ')
  exact ⟨δ, (z1fMap (MonoidHom.id (GQ l)) (resCoef E (chRep T.χ2)) (chRep T.χ2)).2 LinearMap.id (fun _ _ => rfl) δ hδ,
    fun g => congrFun hδp g⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDiag
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Published IsLocalRing Polynomial
open Topology

section SlopeTestRemainingChoices

variable {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B]
  [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B]

omit [IsTopologicalGroup G] in
private theorem cont_ch (κ : G →* Bˣ) (h : Continuous fun g => (κ g : B)) : ContAction (chRep κ) := by
  unfold ReciprocityTheory.Gal.ContAction
  exact (h.comp continuous_fst).mul continuous_snd

omit [IsTopologicalGroup G] in
private theorem cont_col (r : G →* GL (Fin 3) B) (h : ∀ a b, Continuous fun g => (r g : Matrix (Fin 3) (Fin 3) B) a b) :
    ContAction (colRep r) := by
  unfold ReciprocityTheory.Gal.ContAction
  refine continuous_pi fun a => ?_
  change Continuous fun p : G × (Fin 3 → B) => ∑ b, (r p.1 : Matrix (Fin 3) (Fin 3) B) a b * p.2 b
  exact continuous_finset_sum _ fun b _ => ((h a b).comp continuous_fst).mul ((continuous_apply b).comp continuous_snd)

private theorem cr_div (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) (α β γ : G →* Bˣ)
    (hα : Continuous fun g => (α g : B)) (hβ : Continuous fun g => (β g : B)) (hγ : Continuous fun g => (γ g : B))
    (h : ∀ g, γ g * α g = β g) (ha : IsCr φ (chRep α)) (hb : IsCr φ (chRep β)) : IsCr φ (chRep γ) := by
  refine (isCrys_isDR_internalHom φ hφ (chRep α) (chRep β) (chRep γ) (cont_ch α hα) (cont_ch β hβ) (cont_ch γ hγ)
    (LinearMap.mul ℚ_[l] B) (fun g w x => ?_) (fun w w' hw => ?_)).1 ha hb
  · change ((γ g : B) * w) * ((α g : B) * x) = (β g : B) * (w * x)
    rw [← h g, Units.val_mul]
    ring
  · simpa using congrArg (fun f : B →ₗ[ℚ_[l]] B => f 1) hw

private theorem cr_diag (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) (r : G →* GL (Fin 3) B) (κ : Fin 3 → G →* Bˣ)
    (ht : UpperTri r κ) (hc : ∀ a b, Continuous fun g => (r g : Matrix (Fin 3) (Fin 3) B) a b)
    (hr : IsCr φ (colRep r)) (a : Fin 3) : IsCr φ (chRep (κ a)) := by
  have hκ : ∀ a, Continuous fun g => (κ a g : B) := fun a => by
    simpa only [fun g => (ht g).2 a] using hc a a
  have hap : ∀ g x a, colRep r g x a = ∑ b, (r g : Matrix (Fin 3) (Fin 3) B) a b * x b := fun g x a => rfl
  have h10 := fun g => (ht g).1 1 0 (by decide)
  have h20 := fun g => (ht g).1 2 0 (by decide)
  have h21 := fun g => (ht g).1 2 1 (by decide)
  have hch : ∀ (χ : G →* Bˣ) g x, chRep χ g x = (χ g : B) * x := fun _ _ _ => rfl
  have c0 : IsCr φ (chRep (κ 0)) := by
    refine ((isCrys_isDR_sub_quot φ hφ (chRep (κ 0)) (colRep r) (cont_ch _ (hκ 0)) (cont_col r hc)
      (LinearMap.single ℚ_[l] (fun _ : Fin 3 => B) 0) fun g x => ?_).1 (fun x y h => by simpa using congrFun h 0)).1 hr
    funext a
    rw [hap, hch, Fin.sum_univ_three]
    fin_cases a <;> simp [h10, h20, (ht g).2]
  have c2 : IsCr φ (chRep (κ 2)) := by
    refine ((isCrys_isDR_sub_quot φ hφ (colRep r) (chRep (κ 2)) (cont_col r hc) (cont_ch _ (hκ 2))
      (LinearMap.proj 2) fun g x => ?_).2 (fun y => ⟨fun _ => y, rfl⟩)).1 hr
    rw [LinearMap.proj_apply, LinearMap.proj_apply, hap, hch, Fin.sum_univ_three, h20, h21, (ht g).2]
    ring
  have h12 : Continuous fun g => ((κ 1 * κ 2) g : B) := (hκ 1).mul (hκ 2)
  have c12 : IsCr φ (chRep (κ 1 * κ 2)) := by
    refine (admissible_of_bilinear_openSubgroup_galois φ hφ (colRep r) (colRep r) (chRep (κ 1 * κ 2)) (cont_col r hc) (cont_col r hc) (cont_ch _ h12)
      (LinearMap.mk₂ ℚ_[l] (fun x y : Fin 3 → B => x 1 * y 2 - x 2 * y 1) ?_ ?_ ?_ ?_) (fun g x y => ?_) ?_).1 hr hr
    · intro x x' y; simp only [Pi.add_apply]; ring
    · intro c x y; simp only [Pi.smul_apply, smul_mul_assoc, smul_sub]
    · intro x y y'; simp only [Pi.add_apply]; ring
    · intro c x y; simp only [Pi.smul_apply, mul_smul_comm, smul_sub]
    · simp only [LinearMap.mk₂_apply, hap, hch, Fin.sum_univ_three, h10, h20, h21, (ht g).2, MonoidHom.mul_apply,
        Units.val_mul]
      ring
    · refine eq_top_iff.2 fun y _ => Submodule.subset_span ⟨(Pi.single 1 y, Pi.single 2 1), ?_⟩
      simp
  fin_cases a
  · exact c0
  · exact cr_div φ hφ (κ 2) (κ 1 * κ 2) (κ 1) (hκ 2) h12 (hκ 1) (fun g => rfl) c2 c12
  · exact c2

end SlopeTestRemainingChoices

private theorem cr_transport {l : ℕ} [Fact l.Prime] {G G' A V : Type} [Group G] [Group G'] [CommRing A]
    [Algebra ℚ_[l] A] [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V]
    (φ : G →* GQ l) (ρ : Representation A G V) (φ' : G' →* GQ l) (ρ' : Representation A G' V)
    (e : G' → G) (he : Function.Surjective e) (h1 : ∀ g, φ' g = φ (e g)) (h2 : ∀ g, ρ' g = ρ (e g))
    (h : IsCr φ ρ) : IsCr φ' ρ' := by
  have h3 : Dcr φ' (resCoef ℚ_[l] ρ') = Dcr φ (resCoef ℚ_[l] ρ) := by
    unfold Dcr
    refine he.iInf_congr _ fun g => ?_
    unfold actC
    rw [h1]
    change _ = LinearMap.ker (TensorProduct.AlgebraTensorModule.map ((ρ' g).restrictScalars ℚ_[l]) _ - _)
    rw [h2]
    rfl
  have h4 : φ'.range = φ.range := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨e g, (h1 g).symm⟩
    · rintro ⟨g, rfl⟩
      obtain ⟨g, rfl⟩ := he g
      exact ⟨g, h1 g⟩
  unfold IsCr at h ⊢
  rw [h3, h4, h]

theorem UpperTheory.V.Loc.triDiag :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing O E] (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (u : GQ l →* GG 3 B), D.InDtri (π : B →+* E) u → ∀ s ∈ Iq l, ∀ a, (u s).mat a a = algebraMap O B (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a s) := by
  intro l _ O _ _ _ _ _ _ _ D E _ _ _ _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ u hu s hs a
  letI : TopologicalSpace B := moduleTopology ℚ_[l] B
  haveI : IsModuleTopology ℚ_[l] B := ⟨rfl⟩
  haveI : IsTopologicalRing B := IsModuleTopology.isTopologicalRing ℚ_[l] B
  have hG : IsOpen (D.η.ker : Set (GQ l)) := by
    have : D.η.ker = GK D.Kv := Subgroup.ext fun g => D.η_ker g
    rw [this]
    have := D.Kv.2
    exact IntermediateField.fixingSubgroup_isOpen D.Kv.1
  have hφ : IsOpenEmbedding D.η.ker.subtype := hG.isOpenEmbedding_subtypeVal
  let H : Subgroup ↥D.η.ker := D.HL.subgroupOf D.η.ker
  have hH : IsOpen (H : Set ↥D.η.ker) := (hG.inter D.τ_open).preimage continuous_subtype_val
  have hφH : IsOpenEmbedding (D.η.ker.subtype.comp H.subtype) := hφ.comp hH.isOpenEmbedding_subtypeVal
  let r : ↥D.η.ker →* GL (Fin 3) B := glPart D.η u hu.mult
  have hr : ∀ g a b, (r g : Matrix (Fin 3) (Fin 3) B) a b = (u g).mat a b := fun _ _ _ => rfl
  have hlow : ∀ g (a b : Fin 3), b < a → (r g : Matrix (Fin 3) (Fin 3) B) a b = 0 := fun g a b h =>
    hu.tri g a b (by
      have : (b : ℕ) < a := h
      simp only [wt, wt1]
      omega)
  let k : Fin 3 → ↥D.η.ker →* B := fun a =>
    { toFun := fun g => (r g : Matrix (Fin 3) (Fin 3) B) a a
      map_one' := by simp
      map_mul' := fun g h => by
        rw [map_mul, Units.val_mul, Matrix.mul_apply]
        refine Finset.sum_eq_single a (fun b _ hb => ?_) (by simp)
        rcases lt_or_gt_of_ne hb with h' | h'
        · rw [hlow g a b h', zero_mul]
        · rw [hlow h b a h', mul_zero] }
  let κ : Fin 3 → ↥D.η.ker →* Bˣ := fun a => (k a).toHomUnits
  have hκ : ∀ a g, (κ a g : B) = (u g).mat a a := fun _ _ => rfl
  have hc : ∀ a b, Continuous fun g => (r g : Matrix (Fin 3) (Fin 3) B) a b := fun a b =>
    Continuous.comp (hu.cont a b) continuous_subtype_val
  have hcκ : Continuous fun g => (κ a g : B) := hc a a
  let σ : B →ₐ[ℚ_[l]] B := (IsScalarTower.toAlgHom ℚ_[l] E B).comp (π.restrictScalars ℚ_[l])
  have hσ : Continuous σ := IsModuleTopology.continuous_of_linearMap σ.toLinearMap
  let ψ : ↥D.η.ker →* Bˣ := (Units.map (σ : B →* B)).comp (κ a)
  have hψ0 : ∀ g, (ψ g : B) = algebraMap E B (π (κ a g)) := fun _ => rfl
  have hψ : ∀ g, ψ g = Units.map (algebraMap O B : O →* B) (D.Ψ g ^ wt1 a) := fun g => by
    have h1 : (GG.map (π : B →+* E) (u g)).mat a a = (D.rz E g).mat a a := by
      rw [← hu.red]; rfl
    have h2 : (D.rz E g).mat a a = algebraMap O E ((D.Ψ g ^ wt1 a : Oˣ) : O) := by
      change algebraMap O E ((tor O (D.Ψ g) : Matrix (Fin 3) (Fin 3) O) a a) = _
      rw [tor_val, Matrix.diagonal_apply_eq]
    apply Units.ext
    rw [hψ0, hκ]
    change algebraMap E B ((GG.map (π : B →+* E) (u g)).mat a a) = algebraMap O B _
    rw [h1, h2, ← IsScalarTower.algebraMap_apply]
  have hcψ : Continuous fun g => (ψ g : B) := hσ.comp hcκ
  have hcq : Continuous fun g => ((κ a * ψ⁻¹) g : B) := by
    have : (fun g => ((κ a * ψ⁻¹) g : B)) = fun g => (κ a g : B) * (ψ g⁻¹ : B) := by
      funext g
      simp
    rw [this]
    exact hcκ.mul (hcψ.comp continuous_inv)
  obtain ⟨ρ, hρ, hcr⟩ := hu.cr
  have c1 : IsCr (D.η.ker.subtype.comp H.subtype) (colRep (r.comp H.subtype)) := by
    refine cr_transport _ _ _ _ (fun g => (⟨g.1.1, g.2⟩ : ↥D.HL)) (fun g => ⟨⟨⟨g.1, g.2.1⟩, g.2⟩, rfl⟩)
      (fun _ => rfl) (fun g => ?_) hcr
    change Matrix.toLin' _ = Matrix.toLin' _
    rw [hρ]
    rfl
  have c2 : IsCr (D.η.ker.subtype.comp H.subtype) (chRep ((κ a).comp H.subtype)) :=
    cr_diag _ hφH (r.comp H.subtype) (fun a => (κ a).comp H.subtype) (fun g => ⟨hlow g, fun _ => rfl⟩)
      (fun a b => (hc a b).comp continuous_subtype_val) c1 a
  have c3 : IsCr (D.η.ker.subtype.comp H.subtype) (chRep (ψ.comp H.subtype)) := by
    refine crUnr _ hφH _ (cont_ch _ (hcψ.comp continuous_subtype_val)) (D.e * wt1 a) fun g hg x => ?_
    have hτ : D.τ g = 1 := g.2.2
    have h1 : Units.map (algebraMap O B : O →* B) (cycA l l O g) = cycA l l B g := by
      apply Units.ext
      exact (IsScalarTower.algebraMap_apply ℤ_[l] O B _).symm
    have h2 : ψ g = cycA l l B g ^ ((D.e : ℤ) * wt1 a) := by
      rw [hψ, D.Ψ_I g.1.1 hg, hτ, mul_one, map_zpow, map_pow, h1, zpow_mul, zpow_natCast]
    change (ψ g : B) • x = _
    rw [h2]
    rfl
  have c4 : IsCr (D.η.ker.subtype.comp H.subtype) (chRep ((κ a * ψ⁻¹).comp H.subtype)) :=
    cr_div _ hφH _ _ _ (hcψ.comp continuous_subtype_val) (hcκ.comp continuous_subtype_val)
      (hcq.comp continuous_subtype_val) (fun g => by simp) c3 c2
  have key := crUnipChar D.η.ker.subtype hφ (κ a * ψ⁻¹) hcq (fun g => hπ _ (by
      have h1 : ((κ a * ψ⁻¹) g : B) - 1 = ((κ a g : B) - ψ g) * (((ψ g)⁻¹ : Bˣ) : B) := by
        simp [sub_mul]
      rw [h1, map_mul, map_sub, hψ0, AlgHom.commutes]
      simp)) H hH c4 ⟨s, D.η_unr s hs⟩ hs
  have h5 : κ a ⟨s, D.η_unr s hs⟩ = ψ ⟨s, D.η_unr s hs⟩ := by
    simpa [mul_inv_eq_one] using key
  refine (hκ a ⟨s, D.η_unr s hs⟩).symm.trans ?_
  rw [h5, hψ]
  rfl
end

