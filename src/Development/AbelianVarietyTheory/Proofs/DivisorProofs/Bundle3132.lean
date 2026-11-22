import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2633
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2706
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsToPSpaceOfIsSubbundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3085
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3086
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveDegenerationDataIsoOfPolarisedIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3087
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2739
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairBundleFlagCompat
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.VB

namespace GlobalTheory.PairProj

open CategoryTheory.Limits GlobalTheory.LineQuot

section Sub

variable {X : Scheme.{0}} {A B E : X.Modules} {a b r : ℕ}

private theorem rank_cokernel {u : A ⟶ E} (hu : IsSubbundle u) (hA : IsVB A a) (hE : IsVB E r) :
    IsVB (cokernel u) (r - a) := fun x => by
  have : Nonempty X := ⟨x⟩
  obtain ⟨_, s, hs⟩ := hu
  obtain rfl : r = a + s := hE.rank_unique (VBExt.isVB_and_cls_det_of_shortExact X (.mk u (cokernel.π _)
    (cokernel.condition _)) a s { exact := ShortComplex.exact_cokernel _ } hA hs).1
  rw [Nat.add_sub_cancel_left]
  exact hs x

private theorem sub_comp {u : A ⟶ B} {g : B ⟶ E} (hu : IsSubbundle u) (hg : IsSubbundle g) :
    IsSubbundle (u ≫ g) := by
  have := hu.mono
  have := hg.mono
  obtain ⟨s, hs⟩ := hu.isVB_cokernel
  obtain ⟨t, ht⟩ := hg.isVB_cokernel
  exact ⟨inferInstance, _, (VBExt.isVB_and_cls_det_of_shortExact X _ _ _
    (Vert.shortExact_cokernel_comp u g) hs ht).1⟩

private theorem sub_of_comp {u : A ⟶ B} {g : B ⟶ E} {f : A ⟶ E} (w : u ≫ g = f) (hf : IsSubbundle f)
    (hg : IsSubbundle g) (hA : IsVB A a) (hB : IsVB B b) (hE : IsVB E r) (h₁ : a ≤ b) (h₂ : b ≤ r) :
    IsSubbundle u := by
  subst w
  have := hg.mono
  have := hf.mono
  refine ⟨mono_of_mono u g, b - a, VB.isVB_X₁_of_shortExact X _ _ _ (Vert.shortExact_cokernel_comp u g) ?_
    (rank_cokernel hg hB hE)⟩
  have h := rank_cokernel hf hA hE
  rwa [show r - a = b - a + (r - b) by omega] at h

private theorem sub_comp_iso {u : A ⟶ B} (hu : IsSubbundle u) (e : B ⟶ E) [IsIso e] : IsSubbundle (u ≫ e) :=
  have ⟨_, s, hs⟩ := hu
  ⟨inferInstance, s, hs.of_iso (cokernelCompIsIso u e).symm⟩

private theorem exists_le (fl : Vert.Flag E r) (i : Fin (r + 1)) :
    ∀ l : Fin (r + 1), i ≤ l → ∃ t : fl.F i ⟶ fl.F l, t ≫ fl.ι l = fl.ι i := by
  intro l
  induction l using Fin.induction with
  | zero =>
    intro h
    obtain rfl : i = 0 := le_antisymm h (Fin.zero_le _)
    exact ⟨𝟙 _, Category.id_comp _⟩
  | succ l ih =>
    intro h
    rcases h.eq_or_lt with rfl | h
    · exact ⟨𝟙 _, Category.id_comp _⟩
    · obtain ⟨t, ht⟩ := ih (Fin.le_castSucc_iff.2 h)
      exact ⟨t ≫ fl.step l, by rw [Category.assoc, fl.step_ι, ht]⟩

end Sub

variable {B G T Y : Scheme.{0}} {γ : G ⟶ B} {E : B.Modules} {n m₁ m₂ : ℕ} {S P : G.Modules} {s : S ⟶ P}
  {j : P ⟶ (Scheme.Modules.pullback γ).obj E}

private theorem pair_ext (hS : IsVB S m₁) (hP : IsVB P m₂) (hs : IsSubbundle s) (hj : IsSubbundle j)
    (hG : OmitFlag.IsPairBundle γ E m₁ m₂ s j) (g₁ g₂ : T ⟶ G) {g : T ⟶ B} (w₁ : g₁ ≫ γ = g) (w₂ : g₂ ≫ γ = g)
    (h₁ : ∃ e : (Scheme.Modules.pullback g₁).obj S ≅ (Scheme.Modules.pullback g₂).obj S,
      e.hom ≫ (Scheme.Modules.pullback g₂).map (s ≫ j) ≫ (cmp g₂ γ w₂).hom.app E =
        (Scheme.Modules.pullback g₁).map (s ≫ j) ≫ (cmp g₁ γ w₁).hom.app E)
    (h₂ : ∃ e : (Scheme.Modules.pullback g₁).obj P ≅ (Scheme.Modules.pullback g₂).obj P,
      e.hom ≫ (Scheme.Modules.pullback g₂).map j ≫ (cmp g₂ γ w₂).hom.app E =
        (Scheme.Modules.pullback g₁).map j ≫ (cmp g₁ γ w₁).hom.app E) : g₁ = g₂ := by
  obtain ⟨eS, heS⟩ := h₁
  obtain ⟨eP, heP⟩ := h₂
  have hj' := sub_comp_iso (SubPull.isSubbundle_pullback _ _ g₂ _ _ j m₂ hP hj) ((cmp g₂ γ w₂).hom.app E)
  have := hj'.mono
  refine (hG T g _ _ ((Scheme.Modules.pullback g₂).map s) _ (SubPull.isSubbundle_pullback _ _ g₂ _ _ s m₁ hS hs) hj'
    (hS.pullback g₂) (hP.pullback g₂)).unique ⟨w₁, eS, eP, heP, ?_⟩
    ⟨w₂, Iso.refl _, Iso.refl _, Category.id_comp _, by simp⟩
  rw [← cancel_mono ((Scheme.Modules.pullback g₂).map j ≫ (cmp g₂ γ w₂).hom.app E), Category.assoc, Category.assoc,
    heP]
  simpa only [Functor.map_comp, Category.assoc] using heS

private theorem exists_iso_comp {π : Y ⟶ B} (ρ : Y ⟶ G) (wρ : ρ ≫ γ = π) (σ : T ⟶ Y) (υ : T ⟶ G) {g : T ⟶ B}
    (wσ : σ ≫ π = g) (wυ : υ ≫ γ = g) (w : (σ ≫ ρ) ≫ γ = g) {A : G.Modules}
    (u : A ⟶ (Scheme.Modules.pullback γ).obj E) {F : Y.Modules} (ι : F ⟶ (Scheme.Modules.pullback π).obj E)
    {F' : T.Modules} (ι' : F' ⟶ (Scheme.Modules.pullback υ).obj ((Scheme.Modules.pullback γ).obj E))
    (a : (Scheme.Modules.pullback ρ).obj A ≅ F)
    (ha : a.hom ≫ ι = (Scheme.Modules.pullback ρ).map u ≫ (cmp ρ γ wρ).hom.app E)
    (b : (Scheme.Modules.pullback σ).obj F ≅ F')
    (hb : b.hom ≫ ι' ≫ (cmp υ γ wυ).hom.app E = (Scheme.Modules.pullback σ).map ι ≫ (cmp σ π wσ).hom.app E)
    (c : (Scheme.Modules.pullback υ).obj A ≅ F') (hc : c.hom ≫ ι' = (Scheme.Modules.pullback υ).map u) :
    ∃ e : (Scheme.Modules.pullback (σ ≫ ρ)).obj A ≅ (Scheme.Modules.pullback υ).obj A,
      e.hom ≫ (Scheme.Modules.pullback υ).map u ≫ (cmp υ γ wυ).hom.app E =
        (Scheme.Modules.pullback (σ ≫ ρ)).map u ≫ (cmp (σ ≫ ρ) γ w).hom.app E := by
  refine ⟨((cmp σ ρ rfl).app A).symm ≪≫ (Scheme.Modules.pullback σ).mapIso a ≪≫ b ≪≫ c.symm, ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  rw [← hc, Category.assoc, Iso.inv_hom_id_assoc, hb, ← Functor.map_comp_assoc, ha, Functor.map_comp_assoc,
    cmp_assoc σ ρ γ wρ wσ rfl w, Iso.inv_comp_eq, Iso.app_hom, cmp_naturality_assoc]

private theorem exists_sections (hE : IsVB E n) (h₁₂ : m₁ ≤ m₂) (h₂ : m₂ ≤ n) (hS : IsVB S m₁) (hP : IsVB P m₂)
    (hs : IsSubbundle s) (hj : IsSubbundle j) (hG : OmitFlag.IsPairBundle γ E m₁ m₂ s j) (π : Y ⟶ B)
    (fl : ∀ _ : Unit, Vert.Flag ((Scheme.Modules.pullback π).obj E) n)
    (hY : IsFlagBundle π (fun _ : Unit => E) (fun _ => n) fl) :
    ∃ ρ : Y ⟶ G, ρ ≫ γ = π ∧ ∀ x : G, ∃ (U : G.Opens) (σ : U.toScheme ⟶ Y), x ∈ U ∧ σ ≫ ρ = U.ι := by
  let i₁ : Fin (n + 1) := ⟨m₁, by omega⟩
  let i₂ : Fin (n + 1) := ⟨m₂, by omega⟩
  obtain ⟨t, ht⟩ := exists_le (fl ()) i₁ i₂ h₁₂
  obtain ⟨ρ, ⟨wρ, aS, aP, haP, haS⟩, -⟩ := hG Y π _ _ t ((fl ()).ι i₂)
    (sub_of_comp ht ((fl ()).isSubbundle _) ((fl ()).isSubbundle _) ((fl ()).isVB i₁) ((fl ()).isVB i₂)
      (hE.pullback π) h₁₂ h₂) ((fl ()).isSubbundle _) ((fl ()).isVB i₁) ((fl ()).isVB i₂)
  rw [← cmp_hom_app] at haP
  have haS' : aS.hom ≫ (fl ()).ι i₁ = (Scheme.Modules.pullback ρ).map (s ≫ j) ≫ (cmp ρ γ wρ).hom.app E := by
    rw [← ht, reassoc_of% haS, haP, Functor.map_comp_assoc]
  refine ⟨ρ, wρ, fun x => ?_⟩
  obtain ⟨U, hx, flU, cS, cP, hcS, hcP⟩ :=
    FlagTwoSteps.exists_flag_two_steps G _ S P n m₁ m₂ h₁₂ h₂ s j (hE.pullback γ) hS hP hs hj x
  obtain ⟨σ, ⟨wσ, hσ⟩, -⟩ := hY U.toScheme (U.ι ≫ γ) fun _ => flU.ofIso ((cmp U.ι γ rfl).app E)
  obtain ⟨b₁, hb₁⟩ := hσ () i₁
  obtain ⟨b₂, hb₂⟩ := hσ () i₂
  have w : (σ ≫ ρ) ≫ γ = U.ι ≫ γ := by rw [Category.assoc, wρ, wσ]
  exact ⟨U, σ, hx, pair_ext hS hP hs hj hG _ _ w rfl
    (exists_iso_comp ρ wρ σ U.ι wσ rfl w _ _ (flU.ι i₁) aS haS' b₁ hb₁ cS hcS)
    (exists_iso_comp ρ wρ σ U.ι wσ rfl w _ _ (flU.ι i₂) aP haP b₂ hb₂ cP hcP)⟩

private theorem closed_of_sections {Z : Scheme.{0}} (ρ : Y ⟶ G) (f : G ⟶ Z) [IsProper (ρ ≫ f)]
    (h : ∀ x : G, ∃ (U : G.Opens) (σ : U.toScheme ⟶ Y), x ∈ U ∧ σ ≫ ρ = U.ι) :
    UniversallyClosed f ∧ LocallyOfFiniteType f := by
  choose U σ hx hσ using h
  have : Surjective ρ := ⟨fun x => ⟨σ x ⟨x, hx x⟩,
    (Scheme.Hom.comp_apply (σ x) ρ _).symm.trans (by rw [hσ]; rfl)⟩⟩
  refine ⟨UniversallyClosed.of_comp_surjective ρ f, ?_⟩
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFiniteType)
  refine (IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @LocallyOfFiniteType) U
    (eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hx x⟩)).2 fun x => ?_
  have : LocallyOfFiniteType (σ x ≫ ρ) := by rw [hσ]; infer_instance
  have := locallyOfFiniteType_of_comp (σ x) ρ
  rw [← hσ, Category.assoc]
  infer_instance

end GlobalTheory.PairProj

open CategoryTheory.Limits GlobalTheory.PairProj in
theorem _root_.GlobalTheory.T.pair_bundle_flag_compat : ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (B : Scheme.{0}) (q : B ⟶ Sp k), IsProjOver q →
    ∀ (E : B.Modules) (n m₁ m₂ : ℕ), GlobalTheory.VB.IsVB E n → m₁ ≤ m₂ → m₂ ≤ n →
    ∀ (G : Scheme.{0}) (γ : G ⟶ B) (S P : G.Modules) (s : S ⟶ P) (j : P ⟶ (Scheme.Modules.pullback γ).obj E),
      GlobalTheory.VB.IsVB S m₁ → GlobalTheory.VB.IsVB P m₂ → GlobalTheory.VB.IsSubbundle s → GlobalTheory.VB.IsSubbundle j →
      GlobalTheory.OmitFlag.IsPairBundle γ E m₁ m₂ s j → IsProjOver (γ ≫ q) := by
  intro k _ _ B q hq E n m₁ m₂ hE h₁₂ h₂ G γ S P s j hS hP hs hj hG
  obtain ⟨Y, π, fl, hY, hYp⟩ := GlobalTheory.T.exists_flag_bundle_proj_vector_bundle k B q E n hq hE
  obtain ⟨ρ, wρ, hρ⟩ := exists_sections hE h₁₂ h₂ hS hP hs hj hG π fl hY
  have : IsProper (ρ ≫ γ ≫ q) := by
    rw [← Category.assoc, wρ]
    exact (isProper_and_exists_isAmpleLB_of_isProjOver hYp).1
  obtain ⟨_, _⟩ := closed_of_sections ρ (γ ≫ q) hρ
  obtain ⟨N₁, φ₁, hφ₁, H₁⟩ := PluckerMap.exists_toPSpace_of_isSubbundle k B q hq E n m₁ hE (h₁₂.trans h₂) G γ S (s ≫ j)
    hS (sub_comp hs hj)
  obtain ⟨N₂, φ₂, hφ₂, H₂⟩ := PluckerMap.exists_toPSpace_of_isSubbundle k B q hq E n m₂ hE h₂ G γ P j hP hj
  have hPN (N : ℕ) : IsProjOver (PSpace.str k N) := ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩
  have hZ := ProjSpace.isProjOver_pullback (ProjSpace.isProjOver_pullback hq (hPN N₁)) (hPN N₂)
  let ψ₁ : G ⟶ pullback q (PSpace.str k N₁) := pullback.lift γ φ₁ hφ₁.symm
  let ψ : G ⟶ pullback (pullback.fst q (PSpace.str k N₁) ≫ q) (PSpace.str k N₂) :=
    pullback.lift ψ₁ φ₂ (by rw [hφ₂, pullback.lift_fst_assoc])
  have hψ : ψ ≫ pullback.fst _ _ ≫ pullback.fst q (PSpace.str k N₁) ≫ q = γ ≫ q := by
    rw [pullback.lift_fst_assoc, pullback.lift_fst_assoc]
  have : Mono ψ := ⟨fun {T} g₁ g₂ h => by
    have e₀ : g₁ ≫ ψ₁ = g₂ ≫ ψ₁ := by
      simpa only [ψ, Category.assoc, pullback.lift_fst] using h =≫ pullback.fst _ _
    have e₂ : g₁ ≫ φ₂ = g₂ ≫ φ₂ := by
      simpa only [ψ, Category.assoc, pullback.lift_snd] using h =≫ pullback.snd _ _
    have e₁ : g₁ ≫ φ₁ = g₂ ≫ φ₁ := by
      simpa only [ψ₁, Category.assoc, pullback.lift_snd] using e₀ =≫ pullback.snd _ _
    have w : g₁ ≫ γ = g₂ ≫ γ := by
      simpa only [ψ₁, Category.assoc, pullback.lift_fst] using e₀ =≫ pullback.fst _ _
    exact pair_ext hS hP hs hj hG g₁ g₂ w rfl (H₁ T g₁ g₂ _ w rfl e₁) (H₂ T g₁ g₂ _ w rfl e₂)⟩
  have := (isProper_and_exists_isAmpleLB_of_isProjOver hZ).1
  have : IsSeparated (γ ≫ q) := by rw [← hψ]; infer_instance
  have : IsProper (ψ ≫ pullback.fst _ _ ≫ pullback.fst q (PSpace.str k N₁) ≫ q) := by rw [hψ]; exact {}
  have : IsClosedImmersion ψ := (IsClosedImmersion.iff_isProper_and_mono ψ).2 ⟨IsProper.of_comp ψ
    (pullback.fst _ _ ≫ pullback.fst q (PSpace.str k N₁) ≫ q), inferInstance⟩
  rw [← hψ]
  exact ProjSpace.isProjOver_comp_of_isClosedImmersion ψ hZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationKernelKilledOverDvrOfGenericStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisation_kernel_killed_over_dvr_of_generic : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G] (A : Over (Sp L)) [GrpObj A] (φ : A.left ⟶ G.left) (φ₂ : (G2 A).left ⟶ (G2 G).left), IsAbelianScheme G → IsGrpPullback A G (spMap (algebraMap W L)) φ → IsSquare φ φ₂ → ∀ (P : LB (G2 A).left) (P' : LB (G2 G).left), P.IsLB → P'.IsLB → LBIso P (P'.pull φ₂) → (∃ t : (P'.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) → (∃ t : (P'.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → LBIso P' (P'.pull (lift (snd G G) (fst G G)).left) → Out.RelAmple G (P'.pull (lift (𝟙 G) (𝟙 G)).left) → ∀ m : ℕ, (∀ (T : Over (Sp L)) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ m = 1) → ∀ (T : Over (Sp W)) (x : T ⟶ G), (∃ t : (P'.pull (lift (snd G T ≫ x) (fst G T)).left).Gen, t.IsGen) → x ^ m = 1 := by
  first | exact @GlobalTheory.KerExt.kernel_killed | exact GlobalTheory.KerExt.kernel_killed | (intros; apply GlobalTheory.KerExt.kernel_killed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedAbelianSchemeDescendsFiniteTypeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarised_abelian_scheme_descends_finite_type : ∀ (B : Type) [CommRing B] (A : Over (Sp B)) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∃ (B₀ : Subring B) (A₀ : Over (Sp B₀)) (_ : GrpObj A₀) (_ : IsCommMonObj A₀) (φ : A.left ⟶ A₀.left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P₀ : LB (G2 A₀).left), Algebra.FiniteType ℤ B₀ ∧ IsAbelianScheme A₀ ∧ IsGrpPullback A A₀ (spMap B₀.subtype) φ ∧ IsSquare φ φ₂ ∧ P₀.IsLB ∧ LBIso P (P₀.pull φ₂) ∧ (∃ t : (P₀.pull (lift (1 : A₀ ⟶ A₀) (𝟙 A₀)).left).Gen, t.IsGen) ∧ (∃ t : (P₀.pull (lift (𝟙 A₀) (1 : A₀ ⟶ A₀)).left).Gen, t.IsGen) ∧ LBIso P₀ (P₀.pull (lift (snd A₀ A₀) (fst A₀ A₀)).left) ∧ Out.RelAmple A₀ (P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left) := by
  first | (exact @GlobalTheory.PolModel.polarised_descends) | (exact GlobalTheory.PolModel.polarised_descends) | (intros; apply GlobalTheory.PolModel.polarised_descends  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedGenericFibreDescendsGaloisStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarised_generic_fibre_descends_galois : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), ∀ (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, a.act σ ≫ β = β) → ∃ (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A) (κ : pullback G'.hom (jK R') ⟶ pullback G.hom (jK R)), IsMonHom gen.hom ∧ κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β ∧ LBIso (U'.LG.L.pull (pullback.fst G'.hom (jK R'))) (A.L.pull (κ ≫ gen.hom.left)) := by
  first | exact @GlobalTheory.Mum.GenDesc.polarisedGeneric | exact GlobalTheory.Mum.GenDesc.polarisedGeneric | (intros; apply GlobalTheory.Mum.GenDesc.polarisedGeneric <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuoti
section
set_option autoImplicit false

noncomputable section

open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup Coalgebra Bialgebra TensorProduct

namespace GlobalTheory.PDiv.FrobKerOrder

theorem add_pow_of_cast_eq_zero {A : Type*} [CommRing A] {p : ℕ} (hp : p.Prime)
    (h : (p : A) = 0) (x y : A) : (x + y) ^ p = x ^ p + y ^ p := by
  rw [add_pow_prime_eq hp, h]; simp

theorem cast_eq_zero_of_algebra (p : ℕ) (k A : Type*) [CommRing k] [CharP k p] [CommRing A]
    [Algebra k A] : (p : A) = 0 := by
  rw [← map_natCast (algebraMap k A), CharP.cast_eq_zero, map_zero]

variable (p : ℕ) [hp : Fact p.Prime] (k H : Type) [Field k] [CharP k p] [CommRing H]
  [HopfAlgebra k H]

theorem mk_pow_eq (x : H) :
    Ideal.Quotient.mkₐ k (frobKerIdeal p k H) x ^ p =
      algebraMap k _ (counit (R := k) x) ^ p := by
  have hx : x - algebraMap k H (counit (R := k) x) ∈ augIdeal k H := by
    simp [RingHom.mem_ker]
  have h0 : Ideal.Quotient.mkₐ k (frobKerIdeal p k H)
      ((x - algebraMap k H (counit (R := k) x)) ^ p) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (pow_mem_frobKerIdeal hx)
  have e : x = (x - algebraMap k H (counit (R := k) x)) + algebraMap k H (counit (R := k) x) := by
    ring
  conv_lhs => rw [e, ← map_pow, add_pow_of_cast_eq_zero hp.out (cast_eq_zero_of_algebra p k H),
    map_add, h0, zero_add, map_pow, AlgHom.commutes]

theorem map_pow_eq (t : H ⊗[k] H) :
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (frobKerIdeal p k H))
      (Ideal.Quotient.mkₐ k (frobKerIdeal p k H)) t ^ p =
    (1 : H ⧸ frobKerIdeal p k H) ⊗ₜ[k] (Ideal.Quotient.mkₐ k (frobKerIdeal p k H)
      (TensorProduct.lid k H (LinearMap.rTensor H (counit (R := k) (A := H)) t)) ^ p) := by
  induction t with
  | zero => simp [hp.out.ne_zero]
  | add x y hx hy =>
    simp only [map_add]
    rw [add_pow_of_cast_eq_zero hp.out (cast_eq_zero_of_algebra p k _),
      add_pow_of_cast_eq_zero hp.out (cast_eq_zero_of_algebra p k _), hx, hy, tmul_add]
  | tmul x y =>
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_pow, mk_pow_eq,
      LinearMap.rTensor_tmul, TensorProduct.lid_tmul, map_smul, smul_pow, ← map_pow,
      Algebra.algebraMap_eq_smul_one, smul_tmul]

theorem isHopfIdeal : (frobKerIdeal p k H).IsHopfIdeal k where
  counit_eq_zero x hx := frobKerIdeal_le_augIdeal hp.out.ne_zero k H hx
  map_mkQ_comul_eq_zero x hx := by
    have h : frobKerIdeal p k H ≤ RingHom.ker
        ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (frobKerIdeal p k H))
          (Ideal.Quotient.mkₐ k (frobKerIdeal p k H))).comp (comulAlgHom k H)) := by
      refine Ideal.span_le.2 ?_
      rintro _ ⟨a, ha, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, map_pow, AlgHom.comp_apply, map_pow_eq,
        comulAlgHom_apply, rTensor_counit_comul, TensorProduct.lid_tmul, one_smul, ← map_pow]
      have : Ideal.Quotient.mkₐ k (frobKerIdeal p k H) (a ^ p) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 (pow_mem_frobKerIdeal ha)
      rw [this, tmul_zero]
    exact h hx
  antipode_mem x hx := by
    have h : frobKerIdeal p k H ≤ (frobKerIdeal p k H).comap (HopfAlgebra.antipodeAlgHom k H) := by
      refine Ideal.span_le.2 ?_
      rintro _ ⟨a, ha, rfl⟩
      rw [SetLike.mem_coe, Ideal.mem_comap, map_pow]
      apply pow_mem_frobKerIdeal
      have ha' : counit (R := k) a = 0 := ha
      simp [RingHom.mem_ker, ha']
    exact h hx

omit [CharP k p] in
theorem le_sq : frobKerIdeal p k H ≤ augIdeal k H ^ 2 := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨a, ha, rfl⟩
  exact Ideal.pow_le_pow_right hp.out.two_le (Ideal.pow_mem_pow ha p)

theorem pow_le_finrank {n d : ℕ} {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    [Module.Finite K A] (x : Fin d → A)
    (h : RingHom.ker (MvPolynomial.aeval (R := K) x) =
      Ideal.span (Set.range fun i => (MvPolynomial.X i : MvPolynomial (Fin d) K) ^ n)) :
    n ^ d ≤ Module.finrank K A := by
  classical
  let e : (Fin d → Fin n) → (Fin d →₀ ℕ) := fun a => Finsupp.equivFunOnFinite.symm fun i => a i
  have he : Function.Injective e := by
    intro a b hab
    funext i
    have := DFunLike.congr_fun hab i
    exact Fin.ext (by simpa [e] using this)
  have hli : LinearIndependent K fun a : Fin d → Fin n =>
      MvPolynomial.aeval (R := K) x (MvPolynomial.monomial (e a) 1) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg a
    have hmem : (∑ a, g a • MvPolynomial.monomial (e a) (1 : K)) ∈
        RingHom.ker (MvPolynomial.aeval (R := K) x) := by
      rw [RingHom.mem_ker, map_sum]
      simpa only [map_smul] using hg
    have hr : (Set.range fun i => (MvPolynomial.X i : MvPolynomial (Fin d) K) ^ n) =
        (fun s => MvPolynomial.monomial s (1 : K)) '' Set.range (fun i => Finsupp.single i n) := by
      rw [← Set.range_comp]
      congr 1
      funext i
      simp [MvPolynomial.X_pow_eq_monomial]
    rw [h, hr, MvPolynomial.mem_ideal_span_monomial_image] at hmem
    by_contra hne
    have hc : MvPolynomial.coeff (e a) (∑ a, g a • MvPolynomial.monomial (e a) (1 : K)) = g a := by
      simp [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, he.eq_iff]
    obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hmem (e a) (by rw [MvPolynomial.mem_support_iff, hc]; exact hne)
    have h1 := hi i
    have h2 := (a i).2
    simp [e] at h1
    omega
  simpa using hli.fintype_card_le_finrank

theorem pow_finrank_cot_le [Module.Finite k H] :
    p ^ Module.finrank k (Cot k H) ≤ Module.finrank k (H ⧸ frobKerIdeal p k H) := by
  haveI := isHopfIdeal p k H
  set J := frobKerIdeal p k H with hJ
  let π := Ideal.Quotient.mkₐ k J
  have hπ : Function.Surjective π := Ideal.Quotient.mkₐ_surjective k J
  have hε : (counitAlgHom k (H ⧸ J)).comp π = counitAlgHom k H := rfl
  have hbij : Function.Bijective (AugCot.map π hε) := by
    refine ⟨?_, AugCot.map_surjective π hε hπ⟩
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨z, rfl⟩ := (AugCot.exact_kerMap_map π hε hπ y).1 hy
    rw [AugCot.kerMap_apply, AugCot.d_of_mem _ (AugCot.ker_le π hε z.2),
      Ideal.toCotangent_eq_zero]
    exact le_sq p k H (Ideal.Quotient.eq_zero_iff_mem.1 z.2)
  rw [(LinearEquiv.ofBijective _ hbij).finrank_eq]
  set ε := counitAlgHom k (H ⧸ J) with hεdef
  let b := Module.finBasis k (AugCot ε)
  choose x hx using fun i => (RingHom.ker ε).toCotangent_surjective (b i)
  have hsum : ∀ l : Fin (Module.finrank k (AugCot ε)) → k,
      AugCot.d ε (∑ i, l i • (x i : H ⧸ J)) = ∑ i, l i • b i := by
    intro l
    simp [map_sum, hx]
  have hmem : ∀ l : Fin (Module.finrank k (AugCot ε)) → k,
      (∑ i, l i • (x i : H ⧸ J)) ∈ RingHom.ker ε := by
    intro l
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (x i).2
  refine pow_le_finrank (fun i => (x i : H ⧸ J))
    (GlobalTheory.HeightOneHopf.truncated_polynomial p k (H ⧸ J) _ _ ?_ (fun i => (x i).2) ?_ ?_).2
  · intro f hf
    obtain ⟨a, rfl⟩ := hπ f
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (pow_mem_frobKerIdeal (R := k) hf)
  · intro y hy
    refine ⟨b.repr (AugCot.d ε y), ?_⟩
    have h1 : AugCot.d ε (y - ∑ i, b.repr (AugCot.d ε y) i • (x i : H ⧸ J)) = 0 := by
      rw [map_sub, hsum, b.sum_repr, sub_self]
    rwa [AugCot.d_of_mem _ (sub_mem hy (hmem _)), Ideal.toCotangent_eq_zero] at h1
  · intro l hl
    have h1 : AugCot.d ε (∑ i, l i • (x i : H ⧸ J)) = 0 := by
      rw [AugCot.d_of_mem _ (hmem _), Ideal.toCotangent_eq_zero]
      exact hl
    rw [hsum] at h1
    funext i
    exact Fintype.linearIndependent_iff.1 b.linearIndependent l h1 i

end GlobalTheory.PDiv.FrobKerOrder
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesEvalAtNilpotentXEqCoordinate
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

theorem evA_X (k : Type) [CommRing k] (σ : Type) [Finite σ] (A : Type) [CommRing A] [Algebra k A]
    (x : σ → A) (hx : ∀ i, IsNilpotent (x i)) (i : σ) : evA k x hx (X i) = x i := by
  have ha : HasSubst (fun i => (C (x i) : MvPowerSeries Empty A)) :=
    hasSubst_of_constantCoeff_nilpotent fun i => by simpa using hx i
  show (constantCoeff : MvPowerSeries Empty A →+* A) (substAlgHom (R := k) ha (X i)) = x i
  rw [substAlgHom_apply, subst_X ha, constantCoeff_C]

end GlobalTheory.Katz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveAxesDescendFieldStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_axes_descend_field : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (A : Over (Sp K)) [GrpObj A] (B : Over (Sp L)) [GrpObj B] (φ : B.left ⟶ A.left), IsGrpPullback B A (spMap (algebraMap K L)) φ → IsAbelianScheme A → (NoPrimitiveStructureSheafH2 B → NoPrimitiveStructureSheafH2 A) ∧ (AxesVanishingStructureSheafDegOne B → AxesVanishingStructureSheafDegOne A) := by
  first | exact @GlobalTheory.AbCoh.noPrimO2_axesO1_descend | exact GlobalTheory.AbCoh.noPrimO2_axesO1_descend | (intros; apply GlobalTheory.AbCoh.noPrimO2_axesO1_descend <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveDegenerationDataIsoOfPolarisedIsoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_degeneration_data_iso_of_polarised_iso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] [Module O D'.toPre.X] (o : D.toPre.OAct O) (o' : D'.toPre.OAct O) (w : O), TraceFormTwistIso D.toPre o w → TraceFormTwistIso D'.toPre o' w → ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (xe : D'.toPre.X ≃+ D.toPre.X), IsMonHom Φ.hom → ((∀ a, o'.onB.act a ≫ Φ.hom = Φ.hom ≫ o.onB.act a) ∧ (∀ (a : O) x, xe (a • x) = a • xe x) ∧ (∀ x, D'.toPre.c x ≫ Φ.hom = D.toPre.c (xe x))) → (∃ wΛ : (letI := D.toPre.P.isAb.comm; letI := D'.toPre.P.isAb.comm; LB.Iso (abelian₂ D'.toPre.P.A D'.toPre.P.L) ((abelian₂ D.toPre.P.A D.toPre.P.L).pull (lift (fst D'.toPre.P.A D'.toPre.P.A ≫ Φ.hom) (snd D'.toPre.P.A D'.toPre.P.A ≫ Φ.hom) : G2 D'.toPre.P.A ⟶ G2 D.toPre.P.A).left)), wΛ.IsGen ∧ ∀ a b z J J', Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → val (D'.toPre.tau a b) (𝟙 _) z J' = GlobalTheory.PolDeg.lamVal wΛ (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left z J J' * val (D.toPre.tau (xe a) (xe b)) (𝟙 _) z J) → ∃ hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre, hD.xe = xe ∧ hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) = Φ.hom.left := by
  first | exact @GlobalTheory.PrimPull.isPullDeg_of_primitive | exact GlobalTheory.PrimPull.isPullDeg_of_primitive | (intros; apply GlobalTheory.PrimPull.isPullDeg_of_primitive <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelObjectDeterminedOverArtinianPinchStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalSiegelObject_determined_over_artinianPinch : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (β : CommRingCat.of (cycAway n) ⟶ P) (c c' : SiegPre g n (zetaAway n) (Spec.map β)) (c₁ : SiegPre g n (zetaAway n) (Spec.map f₁ ≫ Spec.map β)) (c₂ : SiegPre g n (zetaAway n) (Spec.map f₂ ≫ Spec.map β)), c.Principal → c'.Principal → SiegPB c₁ c (Spec.map f₁) → SiegPB c₁ c' (Spec.map f₁) → SiegPB c₂ c (Spec.map f₂) → SiegPB c₂ c' (Spec.map f₂) → SiegPB c' c (𝟙 _) := by
  first | exact @GlobalTheory.SiegPinch.siegPB_of_pinch | exact GlobalTheory.SiegPinch.siegPB_of_pinch | (intros; apply GlobalTheory.SiegPinch.siegPB_of_pinch <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdFubiniStudyDensitiesEqFlagCellInvariantDensiStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_fubiniStudy_densities_eq_flagCell_invariant_density : ∀ (s : ℕ) (G : Matrix (Fin s) (Fin s) ℂ), G.PosDef → ∀ (y : Low s → ℂ), ∏ i : Fin s, (((s - 1 - i : ℕ).factorial : ℝ) / Real.pi ^ (s - 1 - i : ℕ) * (G.det.re / (leadMinor (upU y * G * (upU y)ᴴ) i).re / grD (upU y * G * (upU y)ᴴ) i ^ ((s - 1 - i : ℕ) + 1))) = GlobalTheory.TrueCx.flagConst s * G.det.re ^ ((s : ℤ) - 1) * GlobalTheory.FlagFibre.dens Gᵀ y := by
  first | exact @GlobalTheory.FlagCellDens.main | exact GlobalTheory.FlagCellDens.main | (intros; apply GlobalTheory.FlagCellDens.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductDegenerationFirstFactorAdjointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_degeneration_first_factor_adjoint : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D₁ D₂ : DegData R I) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → ∀ (i₁ : D₁.toPre.P.A ⟶ D.toPre.P.A) (j₁ : D₁.toPre.X →+ D.toPre.X), i₁ ≫ p₁ = 𝟙 _ → i₁ ≫ p₂ = toUnit _ ≫ η[D₂.toPre.P.A] → (∀ y, q₁ (j₁ y) = y) → (∀ y, q₂ (j₁ y) = 0) → Adj (pol D₁) (pol D) i₁ p₁ j₁ q₁ := by
  first | exact @GlobalTheory.MumProd.adj_inl | exact GlobalTheory.MumProd.adj_inl | (intros; apply GlobalTheory.MumProd.adj_inl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjArithAmbientVerticalOrArithmeticVarietyStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projArithAmbient_vertical_or_arithmeticVariety : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsAmb q → ∀ d : ℕ, topologicalKrullDim Y = d → (∃ (l : ℕ) (_ : Fact l.Prime), Nonempty (Algebra (ZMod l) Γ(Y, ⊤)) ∧ ∀ σ : k →+* ℂ, IsEmpty (CxPts q σ)) ∨ ∃ e : ℕ, d = e + 1 ∧ IsArithVar q e := by
  first | exact @GlobalTheory.MixHt.amb_vertical_or_arithVar | exact GlobalTheory.MixHt.amb_vertical_or_arithVar | (intros; apply GlobalTheory.MixHt.amb_vertical_or_arithVar <;> assumption)
end

