import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PosExact
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Bundle0005
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.CrystallineTwistByUnramifiedCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0013
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0009
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0022
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Bundle0004

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.CocycleMemCrystallineSupSubrepOfPositive
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

theorem GlobalTheory.cocycle_eq_crys_add_sub : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {W : Type} [AddCommGroup W] [Module E W] [Module ℚ_[l] W] [IsScalarTower ℚ_[l] E W] [FiniteDimensional ℚ_[l] W] [TopologicalSpace W] [IsModuleTopology ℚ_[l] W] [IsTopologicalAddGroup W] [ContinuousConstSMul E W] {V : Type} [AddCommGroup V] [Module E V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] E V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul E V] (ρW : Representation E G W) (ρ : Representation E G V), ContAction ρW → ContAction ρ → Positive φ ρW → Positive φ ρ → ∀ i : W →ₗ[E] V, Function.Injective i → (∀ g x, i (ρW g x) = ρ g (i x)) → finrank E ↥(H0dual ((cycA l l E).comp φ) ρW) = finrank E ↥(H0dual ((cycA l l E).comp φ) ρ) → ∀ c ∈ Z1 ρ, ∃ c' ∈ Z1 ρW, (c - fun g => i (c' g)) ∈ finiteCocycles φ ρ := by
  intro hP l _ G _ _ _ φ hφ E _ _ _ _ _ W _ _ _ _ _ _ _ _ _ V _ _ _ _ _ _ _ _ _ ρW ρ hcW hc hpW hp i hi hiρ hdim c hcZ
  obtain ⟨hfinW, hdW⟩ := GlobalTheory.T.finrank_cocycles_eq_crys_add_dual_inv_of_positive hP φ hφ ρW hcW hpW
  obtain ⟨hfin, hd⟩ := GlobalTheory.T.finrank_cocycles_eq_crys_add_dual_inv_of_positive hP φ hφ ρ hc hp
  have hic : Continuous i := IsModuleTopology.continuous_of_linearMap (i.restrictScalars ℚ_[l])
  let S := (finiteCocycles φ ρ).comap (Z1 ρ).subtype
  let SW := (finiteCocycles φ ρW).comap (Z1 ρW).subtype
  let M : Z1 ρW →ₗ[E] Z1 ρ := LinearMap.codRestrict (Z1 ρ) ((LinearMap.compLeft i G).comp (Z1 ρW).subtype)
    (fun c' => ⟨hic.comp c'.2.1, fun g h => by
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.compLeft_apply, Function.comp_apply,
        c'.2.2 g h, map_add, hiρ]⟩)
  have hM : ∀ c' g, ((M c' : Z1 ρ) : G → V) g = i ((c' : G → W) g) := fun _ _ => rfl
  let L : Z1 ρW →ₗ[E] Z1 ρ ⧸ S := S.mkQ ∘ₗ M
  have hker : LinearMap.ker L = SW := by
    ext c'
    simp only [L, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      S, SW, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · intro h
      exact (posExact hP φ hφ ρW ρ hcW hc hpW i hiρ).2 hi hp _ c'.2 h
    · intro h
      exact (z1fMap φ ρW ρ).2 (i.restrictScalars ℚ_[l]) (fun g x => hiρ g x) _ h
  have eW : SW ≃ₗ[E] finiteCocycles φ ρW := Submodule.comapSubtypeEquivOfLe (fun x hx => hx.1)
  have eV : S ≃ₗ[E] finiteCocycles φ ρ := Submodule.comapSubtypeEquivOfLe (fun x hx => hx.1)
  have h1 := LinearMap.finrank_range_add_finrank_ker L
  have h2 := Submodule.finrank_quotient_add_finrank S
  rw [hker, eW.finrank_eq] at h1
  rw [eV.finrank_eq] at h2
  have hr : LinearMap.range L = ⊤ := Submodule.eq_top_of_finrank_eq (by omega)
  obtain ⟨c', hc'⟩ : S.mkQ ⟨c, hcZ⟩ ∈ LinearMap.range L := hr ▸ Submodule.mem_top
  refine ⟨c', c'.2, ?_⟩
  have := (Submodule.Quotient.eq S).1 hc'.symm
  simp only [S, Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub] at this
  exact this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.CrystallineTwistByUnramifiedCharacterStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_twist_by_unramified_character : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (u : GQ l →* Bˣ), QCont l (fun g => (u g : B)) → (∀ g ∈ Iq l, u g = 1) → (∀ g, IsNilpotent ((u g : B) - 1)) → D.InDcr (π : B →+* E) (r0 D.η ((Units.map (algebraMap O B : O →* B)).comp D.Ψ * u)) := by
  first | exact @GlobalTheory.OrdTwist.twist_inDcr | exact GlobalTheory.OrdTwist.twist_inDcr | (intros; apply GlobalTheory.OrdTwist.twist_inDcr <;> assumption)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.DiagonalizeOfDistinctEigenvalues
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

theorem GlobalTheory.crystalline_cocycle_twisted_extension_of_quotient : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (e : ℕ), 1 ≤ e → ∀ (κ : Fin 3 → G →* Bˣ), (∀ i, Continuous fun g => (κ i g : B)) → (∀ g, φ g ∈ Iq l → ∀ i, κ i g = cycA l l B (φ g) ^ ((e : ℤ) * wt1 i)) → ∀ (x : G → B) (hx : ∀ g h, x (g * h) = x g + ((κ 0 / κ 1) g : Bˣ) * x h), Continuous x → IsCr φ (ext2 (κ 0) (κ 1) x hx) → ∀ y z : G → B, (fun g => (z g, y g)) ∈ Z1 (twist (κ 2)⁻¹ (ext2 (κ 0) (κ 1) x hx)) → y ∈ finiteCocycles φ (chRep (κ 1 / κ 2)) → (fun g => (z g, y g)) ∈ finiteCocycles φ (twist (κ 2)⁻¹ (ext2 (κ 0) (κ 1) x hx)) := by
  intro hP l _ G _ _ _ φ hφ E _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ e he κ hκc hine x hx hxc hcr y z hzy hy
  haveI : ContinuousConstSMul E B := contConstSMul_alg E
  haveI : Module.Finite E B := Module.Finite.of_restrictScalars_finite ℚ_[l] E B
  have w0 : wt1 0 = 1 := rfl
  have w1 : wt1 1 = 0 := rfl
  have w2 : wt1 2 = -1 := rfl
  have cd : ∀ i j, Continuous fun g => (((κ i / κ j) g : Bˣ) : B) := fun i j => cont_char_div (hκc i) (hκc j)
  have ined : ∀ i j g, φ g ∈ Iq l →
      (κ i / κ j) g = cycA l l B (φ g) ^ ((e : ℤ) * wt1 i - (e : ℤ) * wt1 j) := fun i j g hg => by
    rw [MonoidHom.div_apply, hine g hg i, hine g hg j, zpow_sub, div_eq_mul_inv]
  have crk : ∀ i, IsCr φ (chRep (κ i)) := fun i =>
    crUnr φ hφ _ (contAction_chRep (hκc i)) ((e : ℤ) * wt1 i) fun g hg v => by
      rw [chRep_apply, hine g hg, smul_eq_mul]
  have crd : ∀ i j, IsCr φ (chRep (κ i / κ j)) := fun i j =>
    crUnr φ hφ _ (contAction_chRep (cd i j)) ((e : ℤ) * wt1 i - (e : ℤ) * wt1 j) fun g hg v => by
      rw [chRep_apply, ined i j g hg, smul_eq_mul]
  have hxf := (UpperTheory.isCrystalline_extension_iff_mem_finiteCocycles φ hφ _ _ (hκc 0) (hκc 1) x hx hxc (crk 0) (crk 1)).1 hcr
  have ed : (κ 0 / κ 2) / (κ 1 / κ 2) = κ 0 / κ 1 := div_div_div_cancel_right _ _ _
  have hx' : ∀ g h, x (g * h) = x g + (((κ 0 / κ 2) / (κ 1 / κ 2)) g : Bˣ) * x h := by rw [ed]; exact hx
  have eM : twist (κ 2)⁻¹ (ext2 (κ 0) (κ 1) x hx) = ext2 (κ 0 / κ 2) (κ 1 / κ 2) x hx' := by
    refine MonoidHom.ext fun g => LinearMap.ext fun v => ?_
    simp only [twist_apply, characterExtensionRep_apply, div_eq_mul_inv, MonoidHom.mul_apply, Units.val_mul, Prod.smul_mk, smul_eq_mul]
    ext <;> simp only [] <;> ring
  rw [eM] at hzy ⊢
  set M := ext2 (κ 0 / κ 2) (κ 1 / κ 2) x hx' with hM
  have cM : ContAction M := contAction_charExtension_of_continuous_cocycle (cd 0 2) (cd 1 2) hx' hxc
  have crM : IsCr φ M :=
    (UpperTheory.isCrystalline_extension_iff_mem_finiteCocycles φ hφ _ _ (cd 0 2) (cd 1 2) x hx' hxc (crd 0 2) (crd 1 2)).2 (by rw [ed]; exact hxf)
  have hin02 : ∀ g, φ g ∈ Iq l → (κ 0 / κ 2) g = cycA l l B (φ g) ^ (2 * (e : ℤ)) := fun g hg => by
    rw [ined 0 2 g hg, w0, w2]; congr 1; ring
  have hin12 : ∀ g, φ g ∈ Iq l → (κ 1 / κ 2) g = cycA l l B (φ g) ^ (e : ℤ) := fun g hg => by
    rw [ined 1 2 g hg, w1, w2]; congr 1; ring
  have pM : Positive φ (resCoef E M) := ⟨(isCrys_isDR_restrict_openSubgroup φ hφ _ cM).1 crM,
    GlobalTheory.T.filtBy_positiveWeight_of_two_character_extension φ hφ π hπ (κ 0 / κ 2) (κ 1 / κ 2) (cd 0 2) (cd 1 2) (2 * (e : ℤ)) e (by omega)
      (by exact_mod_cast he) hin02 hin12 x hx'⟩
  obtain ⟨c, hc, hcy⟩ := (posExact hP φ hφ (resCoef E M) (resCoef E (chRep (κ 1 / κ 2))) cM
    (contAction_chRep (cd 1 2)) pM (LinearMap.snd E B B) (fun g v => rfl)).1 Prod.snd_surjective y hy
  have hcM : c ∈ UpperTheory.V.Loc.finiteCocycles φ M := hc
  have hc2 : ∀ g, (c g).2 = y g := fun g => congrFun hcy g
  have hzc : Continuous z := hzy.1.fst
  have hcc : Continuous fun g => (c g).1 := hcM.1.1.fst
  have hzm : ∀ g h, z (g * h) =
      z g + ((((κ 0 / κ 2) g : Bˣ) : B) * z h + x g * ((κ 1 / κ 2) g : Bˣ) * y h) := fun g h =>
    congrArg Prod.fst (hzy.2 g h)
  have hcm : ∀ g h, (c (g * h)).1 =
      (c g).1 + ((((κ 0 / κ 2) g : Bˣ) : B) * (c h).1 + x g * ((κ 1 / κ 2) g : Bˣ) * y h) := fun g h => by
    rw [← hc2 h]
    exact congrArg Prod.fst (hcM.1.2 g h)
  have hd : z - (fun g => (c g).1) ∈ Z1 (chRep (κ 0 / κ 2)) := by
    refine ⟨hzc.sub hcc, fun g h => ?_⟩
    simp only [Pi.sub_apply, hzm, hcm, chRep_apply]
    ring
  have hd' : z - (fun g => (c g).1) ∈ Z1 (resCoef E (chRep (κ 0 / κ 2))) := hd
  obtain ⟨hcχ, pχ⟩ := GlobalTheory.T.positive_scalar_rep_of_character_positive_weight φ hφ π hπ (κ 0 / κ 2) (cd 0 2) (2 * (e : ℤ)) (by omega) hin02
    (resCoef E (chRep (κ 0 / κ 2))) (fun g v => rfl)
  obtain ⟨hfin, hdim⟩ := GlobalTheory.T.finrank_cocycles_eq_crys_add_dual_inv_of_positive hP φ hφ (resCoef E (chRep (κ 0 / κ 2))) hcχ pχ
  have hinj : Function.Injective (algebraMap ℤ_[l] E) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] E]
    exact (algebraMap ℚ_[l] E).injective.comp Subtype.val_injective
  have hD : H0dual ((cycA l l E).comp φ) (resCoef E (chRep (κ 0 / κ 2))) = ⊥ := by
    have hopen : IsOpen ((φ.range : Subgroup (GQ l)) : Set (GQ l)) := by
      rw [MonoidHom.coe_range]; exact hφ.isOpen_range
    obtain ⟨s, ⟨⟨g, rfl⟩, hs⟩, hfo⟩ := ((cycInertia l).2 φ.range hopen).2
    refine eq_bot_iff.2 fun F hF => ?_
    rw [Submodule.mem_bot]
    refine LinearMap.ext fun v => ?_
    have h1 := hF g v
    simp only [MonoidHom.comp_apply] at h1
    have hχg : (((κ 0 / κ 2) g : Bˣ) : B) = algebraMap E B (((cycA l l E (φ g)) ^ (2 * (e : ℤ)) : Eˣ) : E) := by
      rw [hin02 g hs, ← algebraMap_cycA (E := E) (B := B), ← map_zpow]; rfl
    have h2 : F (resCoef E (chRep (κ 0 / κ 2)) g v) = (((cycA l l E (φ g)) ^ (2 * (e : ℤ)) : Eˣ) : E) * F v := by
      change F ((((κ 0 / κ 2) g : Bˣ) : B) * v) = _
      rw [hχg, ← Algebra.smul_def, map_smul, smul_eq_mul]
    rw [h2] at h1
    have hne : cycA l l E (φ g) ^ (2 * (e : ℤ)) ≠ cycA l l E (φ g) := by
      intro h
      have h3 : cyc l l (φ g) ^ (2 * (e : ℤ) - 1) = 1 := by
        apply Units.map_injective (f := (algebraMap ℤ_[l] E : ℤ_[l] →* E)) hinj
        rw [map_zpow, map_one]
        change cycA l l E (φ g) ^ (2 * (e : ℤ) - 1) = 1
        rw [zpow_sub_one, h, mul_inv_cancel]
      exact hfo (isOfFinOrder_iff_zpow_eq_one.2 ⟨_, by omega, h3⟩)
    have h4 : ((((cycA l l E (φ g)) ^ (2 * (e : ℤ)) : Eˣ) : E) - (cycA l l E (φ g) : E)) * F v = 0 := by
      rw [sub_mul, h1, sub_self]
    rcases mul_eq_zero.1 h4 with h5 | h5
    · exact absurd (Units.ext (sub_eq_zero.1 h5)) hne
    · simpa using h5
  rw [hD, finrank_bot, add_zero] at hdim
  have hle : UpperTheory.V.Loc.finiteCocycles φ (resCoef E (chRep (κ 0 / κ 2))) ≤ Z1 (resCoef E (chRep (κ 0 / κ 2))) :=
    fun c h => h.1
  haveI := hfin
  have heq := Submodule.eq_of_le_of_finrank_eq hle hdim.symm
  have hdf : z - (fun g => (c g).1) ∈ UpperTheory.V.Loc.finiteCocycles φ (chRep (κ 0 / κ 2)) := by
    rw [← heq] at hd'
    exact (z1fMap φ (resCoef E (chRep (κ 0 / κ 2))) (chRep (κ 0 / κ 2))).2 LinearMap.id (fun _ _ => rfl) _ hd'
  have inl : ∀ g v, LinearMap.inl E B B (chRep (κ 0 / κ 2) g v) = M g (LinearMap.inl E B B v) := fun g v => by
    simp [hM, characterExtensionRep_apply, chRep_apply]
  have h1 := (z1fMap φ (chRep (κ 0 / κ 2)) M).2 ((LinearMap.inl E B B).restrictScalars ℚ_[l]) inl _ hdf
  have h2 := add_mem h1 hcM
  convert h2 using 1
  funext g
  ext <;> simp [hc2]
end

