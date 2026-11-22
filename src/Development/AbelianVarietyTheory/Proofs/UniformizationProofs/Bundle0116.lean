import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0102
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0112
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0098
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0003
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0090
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0096
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0018
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0056
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0061
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0094
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0084

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecPullNeZero
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AmpleCrit

variable {X X' : Scheme.{0}}

theorem pull_pw_eq (M : LB X) (π : X' ⟶ X) (t : ℤ) :
    (AbLaw.pw M t).pull π = AbLaw.pw (M.pull π) t := by
  refine congrArg (LB.mk (M.pull π).ι (M.pull π).U) ?_
  funext j j'
  change ∏ _k : PUnit, _ = (∏ _k : PUnit, _) ^ t
  refine Eq.trans ?_ (Finset.prod_zpow
    (G := Γ(X', LB.wchart M (fun _ : PUnit => π) j ⊓ LB.wchart M (fun _ : PUnit => π) j')ˣ) _ _ t)
  refine Finset.prod_congr rfl fun k _ => ?_
  refine (zpow_one _).trans (Eq.trans ?_ (congrArg (· ^ t) (zpow_one _)).symm)
  exact (congrArg (res _) (map_zpow (pullU π _) (M.g (j k) (j' k)) t)).trans (map_zpow (res _) _ t)

theorem pw_pw_eq (M : LB X) (a b : ℤ) : AbLaw.pw (AbLaw.pw M a) b = AbLaw.pw M (a * b) := by
  simp only [AbLaw.pw, zpow_mul]
  rfl

theorem injective_stalkMap (π : X' ⟶ X) [Flat π] (z : X') : Function.Injective (π.stalkMap z).hom := by
  algebraize [(π.stalkMap z).hom]
  have : Module.Flat (X.presheaf.stalk (π z)) (X'.presheaf.stalk z) := Flat.stalkMap π z
  have : IsLocalHom (algebraMap (X.presheaf.stalk (π z)) (X'.presheaf.stalk z)) :=
    inferInstanceAs (IsLocalHom (π.stalkMap z).hom)
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom
    (A := X.presheaf.stalk (π z)) (B := X'.presheaf.stalk z)
  exact FaithfulSMul.algebraMap_injective _ _

theorem gs_zero' (π : X' ⟶ X) (z : X') (U : X.Opens) (h : π z ∈ U) : gs π z U 0 = 0 := by
  rw [gs_eq π z U h, map_zero, map_zero]

theorem exists_sec_pull_ne_zero (π : X' ⟶ X) [Flat π] [Surjective π] {M : LB X} (hM : M.IsLB)
    (s : LB.Sec M) (hs : ∃ j, s.f j ≠ 0) : ∃ s' : LB.Sec (M.pull π), ∃ j, s'.f j ≠ 0 := by
  have hM' := pull_isLB hM π
  obtain ⟨⟨s', hs', -⟩, -⟩ := SecPullIso.section_pull X X' π M (M.pull π) _ hM hM'
    (CubePf.idIsoL_isGen hM') s
  refine ⟨s', ?_⟩
  by_contra h
  push Not at h
  obtain ⟨j, hj⟩ := hs
  refine hj (fn_ext fun x hx => ?_)
  obtain ⟨z, rfl⟩ := π.surjective x
  have hz : z ∈ (M.pull π).U (fun _ => j) := mem_pull.2 hx
  have e := hs' z j (fun _ => j) hx hz
  have e₀ : gs (𝟙 X') z ((M.pull π).U fun _ => j) (s'.f fun _ => j) = 0 :=
    (congrArg (gs (𝟙 X') z _) (h fun _ => j)).trans (gs_zero' _ z _ hz)
  replace e := e.trans ((congrArg _ e₀).trans (mul_zero _))
  rw [gs_stalkMap π z _ hx] at e
  rw [gs_zero' (𝟙 X) (π z) _ hx]
  exact injective_stalkMap π z (e.trans (map_zero _).symm)

def zeroSec (M : LB X) : LB.Sec M := ⟨fun _ => 0, fun _ _ => by rw [map_zero, map_zero, mul_zero]⟩

theorem exists_cover_of_pull {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') (hg : g.Flat)
    [CompactSpace X] [QuasiSeparatedSpace X] (f : X ⟶ Spec (CommRingCat.of R)) (π : X' ⟶ X)
    (f' : X' ⟶ Spec (CommRingCat.of R')) (h : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
    [Surjective π] {M : LB X} (hM : M.IsLB) {n : ℕ} (t : Fin (n + 1) → LB.Sec (M.pull π))
    (ht : ⨆ i, nonzeroLocus (t i) = ⊤) :
    ∃ (m : ℕ) (u : Fin (m + 1) → LB.Sec M), ⨆ i, nonzeroLocus (u i) = ⊤ := by
  choose m c u hu using fun i => FlatSec.exists_comb_of_flat R R' g hg X f X' π f' h M hM (t i)
  let I := Σ i, Fin (m i)
  let e : Option I ≃ Fin (Fintype.card I + 1) := Fintype.equivFinOfCardEq Fintype.card_option
  let v : Option I → LB.Sec M := fun o => o.elim (zeroSec M) fun q => u q.1 q.2
  refine ⟨Fintype.card I, fun a => v (e.symm a), top_le_iff.1 fun x _ => ?_⟩
  obtain ⟨z, rfl⟩ := π.surjective x
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
    (show z ∈ ⨆ i, nonzeroLocus (t i) by rw [ht]; trivial)
  obtain ⟨J, hJ, hun⟩ := (mem_nonzeroLocus _ _).1 hi
  have hk : π z ∈ M.U (J PUnit.unit) := mem_pull.1 hJ
  have e₁ := hu i z (J PUnit.unit) hk
  have hun' := (congrArg IsUnit e₁).mp hun
  obtain ⟨a, -, ha⟩ := IsLocalRing.exists_of_isUnit_sum hun'
  have ha' := isUnit_of_mul_isUnit_right ha
  rw [gs_stalkMap π z _ hk] at ha'
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨e (some ⟨i, a⟩), ?_⟩
  beta_reduce
  rw [Equiv.symm_apply_apply]
  exact (mem_nonzeroLocus _ _).2 ⟨_, hk, (isUnit_map_iff (π.stalkMap z).hom _).1 ha'⟩

theorem exists_map {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) {M : LB X} (hM : M.IsLB)
    {n : ℕ} (t : Fin (n + 1) → LB.Sec M) (ht : ⨆ i, nonzeroLocus (t i) = ⊤) :
    ∃ (P : Scheme.{0}) (q : P ⟶ Spec (CommRingCat.of R)) (H : LB P) (φ : X ⟶ P), IsProper q ∧ H.IsLB ∧
      φ ≫ q = f ∧ LBIso M (H.pull φ) ∧
      ∀ i, ∃ V : P.Opens, IsAffineOpen V ∧ nonzeroLocus (t i) = φ ⁻¹ᵁ V := by
  obtain ⟨P, q, H, s, hH, hva, heq⟩ := ProjQuot.exists_veryAmpleBy_of_ideal R n ⊥ (fun F hF d => by
    rw [Ideal.mem_bot] at hF ⊢
    rw [hF, map_zero])
  obtain ⟨φ, w, hφ, hw, hs⟩ := exists_hom_of_veryAmpleBy R P q H n s hH hva X f M t hM ht (fun d F hF h0 k => by
    obtain ⟨a, ha⟩ := (heq d F hF).1 h0 0
    rw [Ideal.mem_bot] at ha
    have : F = 0 := ((MvPolynomial.isRegular_X (n := (0 : Fin (n + 1))) (R := R)).pow a).left
      (ha.trans (mul_zero _).symm)
    rw [this, map_zero])
  exact ⟨P, q, H, φ, isProper_of_isProjBy R P q ⟨H, hH, n, s, hva⟩, hH, hφ, ⟨w, hw⟩, fun i =>
    ⟨_, (hva.2 i).1, (SecPullIso.section_pull P X φ H M w hH hM hw (s i)).2 (t i) (hs i)⟩⟩

theorem triv_translDiff_push {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A']
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) {L : LB A.left} (hL : L.IsLB) {T' : Over S'}
    (x : T' ⟶ A') (hx : Triv (translDiff A' (L.pull φ) x)) : Triv (translDiff A L (pushPt h.1.w x)) := by
  obtain ⟨c, hc⟩ := hx
  have hL' := pull_isLB hL φ
  let T : Over S := Over.mk (T'.hom ≫ f)
  let T₂ : Over S' := Over.mk ((fst T A).left ≫ T'.hom)
  have sq : (snd T A).left ≫ A.hom = ((fst T A).left ≫ T'.hom) ≫ f :=
    pullback.condition.symm.trans (Category.assoc _ _ _).symm
  let a : T₂ ⟶ T' := Over.homMk (fst T A).left rfl
  let b : T₂ ⟶ A' := Over.homMk (h.1.lift _ _ sq) (h.1.lift_snd _ _ _)
  have hb : b.left ≫ φ = (snd T A).left := h.1.lift_fst _ _ _
  have k₂ : (lift a b).left ≫ (snd T' A').left ≫ φ = (snd T A).left :=
    (Category.assoc _ _ _).symm.trans ((congrArg (fun q => q.left ≫ φ) (lift_snd a b)).trans hb)
  have k₃ : (lift a b).left ≫ ((fst T' A' ≫ x) * snd T' A').left ≫ φ =
      ((fst T A ≫ pushPt h.1.w x) * snd T A).left := by
    have e : lift a b ≫ ((fst T' A' ≫ x) * snd T' A') = (a ≫ x) * b := by
      rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]
    let j : Over.mk (T₂.hom ≫ f) ⟶ T ⊗ A := Over.homMk (𝟙 _) ((Category.id_comp _).trans
      ((Over.w (snd T A)).symm.trans sq))
    have e₁ := h.2 T₂ (a ≫ x) b (j ≫ fst T A ≫ pushPt h.1.w x) (j ≫ snd T A)
      ((Category.id_comp _).trans (Category.assoc _ _ _).symm) ((Category.id_comp _).trans hb.symm)
    rw [← MonObj.comp_mul, ← e] at e₁
    exact (Category.assoc _ _ _).symm.trans (e₁.symm.trans (Category.id_comp _))
  obtain ⟨c₂, h₂, -⟩ := exists_up ((isGen_iff _).1 (CubePf.idIsoL_isGen hL')) hL hL' c hc
  refine gen_chartPull (chartPullSame L _ _ _ (lift a b).left fun k => ?_) c₂ h₂
  fin_cases k
  exacts [k₃.symm, k₂.symm]

theorem relAmple_of_effective : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → ∀ (R : Type) [CommRing R], IsField R → ∀ (B : Over (Spec (CommRingCat.of R))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ (L : RigLB B) (_ : CubicalStr B L) (k : ℕ) (s : LB.Sec (pw L.L k)), 1 ≤ k → (∃ j, s.f j ≠ 0) → ∀ (K : Type) [Field K] [IsAlgClosed K] (p : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) (n : ℕ), n.Prime → (n : K) ≠ 0 → ¬ n ∣ 2 * k → (∀ x : Over.mk p ⟶ B, x ^ n = 1 → Triv (translDiff B L.L x) → x = 1) → RelAmple B L.L := by
  intro hcount R _ hR B _ _ hB L c k s hk hs K _ _ p n hn hnK hnk hx
  obtain ⟨g, rfl⟩ : ∃ g : R →+* K, p = Spec.map (CommRingCat.ofHom g) :=
    ⟨(Spec.preimage p).hom, (Spec.map_preimage p).symm⟩
  have hg : g.Flat := RingHom.Flat.of_isField hR g
  set p := Spec.map (CommRingCat.ofHom g) with hp
  have : Flat p := (HasRingHomProperty.Spec_iff (P := @Flat)).2 hg
  have : Surjective p := ⟨fun y => by
    let := hR.toField
    have : Subsingleton (Spec (CommRingCat.of R)) := inferInstanceAs (Subsingleton (PrimeSpectrum R))
    exact ⟨(default : PrimeSpectrum K), Subsingleton.elim _ _⟩⟩
  have := hB.proper
  let B' : Over (Spec (CommRingCat.of K)) := (Over.pullback p).obj B
  let π : B'.left ⟶ B.left := pullback.fst B.hom p
  have h : IsGrpPullback B' B p π := isGrpPullback_pullback B p
  have : IsCommMonObj B' := PolPull.isCommMonObj_of_isGrpPullback h
  have hB' := PolPull.isAbelianScheme_of_isGrpPullback hB h
  have : Flat π := MorphismProperty.of_isPullback (P := @Flat) h.1.flip inferInstance
  have : Surjective π := MorphismProperty.of_isPullback (P := @Surjective) h.1.flip inferInstance
  obtain ⟨hL', hr, ⟨c', -⟩, -⟩ := CubePf.cubePull _ _ B B' (cubeMapOf h) L c

  have hsec : ∃ s' : LB.Sec (AbLaw.pw (L.L.pull π) k), ∃ j, s'.f j ≠ 0 :=
    pull_pw_eq L.L π k ▸ exists_sec_pull_ne_zero π (isLB_pw L.isLB k) s hs
  obtain ⟨s', hs'⟩ := hsec
  have hcov : ∃ (m : ℕ) (t : Fin (m + 1) → LB.Sec ((AbLaw.pw L.L (2 * k : ℕ)).pull π)),
      ⨆ i, nonzeroLocus (t i) = ⊤ := by
    rw [pull_pw_eq]
    exact CubeFree.exists_cover_nonzeroLocus K B' hB' ((cubeMapOf h).rigLB L hL' hr) c' k s' hs'
  obtain ⟨m', t', ht'⟩ := hcov
  have hM := isLB_pw L.isLB (2 * k : ℕ)
  have : CompactSpace B.left := QuasiCompact.compactSpace_of_compactSpace B.hom
  have : QuasiSeparatedSpace B.left := quasiSeparatedSpace_of_quasiSeparated B.hom
  obtain ⟨m, t, ht⟩ := exists_cover_of_pull g hg B.hom π B'.hom h.1 hM t' ht'
  obtain ⟨P, q, H, φ, hq, hH, hφ, hiso, hloc⟩ := exists_map B.hom hM t ht

  let Z : Over (Spec (CommRingCat.of K)) := Over.mk (pullback.snd q p)
  let ρ : Z.left ⟶ P := pullback.fst q p
  let φ' : B' ⟶ Z := Over.homMk (pullback.lift (π ≫ φ) B'.hom (by rw [Category.assoc, hφ]; exact h.1.w))
    (pullback.lift_snd _ _ _)
  have hφ' : φ'.left ≫ ρ = π ≫ φ := pullback.lift_fst _ _ _
  have hZ : IsPullback ρ Z.hom q p := IsPullback.of_hasPullback q p
  have hsq : IsPullback π φ'.left φ ρ := by
    refine IsPullback.of_bot ?_ hφ'.symm hZ
    rw [Over.w φ', hφ]
    exact h.1
  have : IsProper Z.hom := MorphismProperty.of_isPullback (P := @IsProper) hZ hq
  have : Surjective ρ := MorphismProperty.of_isPullback (P := @Surjective) hZ.flip inferInstance
  have hqf' : LocallyQuasiFinite φ'.left := by
    refine GlobalTheory.T.locallyQuasiFinite_of_cubical_pow_iso_pull hcount K B' hB' ((cubeMapOf h).rigLB L hL' hr) c' (2 * k) n hn hnK hnk
      (fun x hxn htr => ?_) Z φ' (H.pull ρ) (pull_isLB hH ρ) ?_
    · have key : ∀ p' : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R), p' = p →
          ∀ y : Over.mk p' ⟶ B, y ^ n = 1 → Triv (translDiff B L.L y) → y = 1 := by
        rintro _ rfl
        exact hx
      have e : pushHom h _ x = 1 := key _ (Category.id_comp p) (pushHom h _ x)
        (by rw [← map_pow, hxn, map_one]) (triv_translDiff_push h L.isLB x htr)
      have e' := e.trans (map_one (pushHom h (baseOver _))).symm
      exact Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun q => q.left) e') (by rw [Over.w, Over.w]))
    · show LBIso (AbLaw.pw (L.L.pull π) (2 * k : ℕ)) ((H.pull ρ).pull φ'.left)
      rw [← pull_pw_eq]
      exact LBIso.chartPull (Geo.Tor.chartPullPull _ π π rfl)
        (chartPullLinComb H ρ (fun _ => φ'.left) (fun _ => φ) (fun _ => 1) π fun _ => hφ') hiso
  have : IsProper (φ ≫ q) := hφ ▸ hB.proper
  have : IsProper φ := IsProper.of_comp φ q
  have : LocallyQuasiFinite φ := Unif.locallyQuasiFinite_of_isPullback_surjective _ _ _ _ φ φ'.left π ρ hsq
    inferInstance inferInstance inferInstance hqf'
  have : IsFinite φ := IsFinite.of_isProper_of_locallyQuasiFinite φ
  have hva := veryAmpleBy_pw_of_affine_loci R B.left B.hom _ m t hM ht fun i => by
    obtain ⟨V, hV, e⟩ := hloc i
    rw [e]
    exact hV.preimage φ
  obtain ⟨d, hd, hva⟩ := hva
  rw [pw_pw_eq, ← Nat.cast_mul] at hva
  exact (Unif.relAmple_iff_veryAmpleBy R B L.L L.isLB).2
    ⟨2 * k * d, Nat.mul_pos (by omega) hd, hva⟩

end GlobalTheory.AmpleCrit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LineBundleSectionsTorusTorsionWeightSpaces
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.UU.Weight

open GlobalTheory.TorusExt GlobalTheory.ClassWeight

abbrev SecA {R : Type} [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k : ℕ) : Type :=
  SecMod (F := F) (fst (TFK (R := R) F) A.A).left (LPow A.A A.L (k : ℤ) (TFK (R := R) F))

theorem exists_expansion (hL : Laws) (hL₂ : Laws2) : AllPre fun {V} _ _ _ {D} {A} {_} _ _ U =>
    ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k →
      ∃ S : ∀ α, SecA A F k →ₗ[F] CompMod D F k α,
        (∀ (v : SecA A F k) (s : Raw D F k), U.ExpF F k v.sec s ↔ s = fun α => (S α v).sec) ∧
        ∀ v, (∀ α, S α v = 0) → v = 0 := by
  intro V _ _ _ hV D A G _ _ U F _ _ k hk
  choose x hx using GlobalTheory.T.exists_fourierJacobi_expansion_over_field hL hL₂ V hV D A G U F k hk
  have uq := GlobalTheory.T.fourierJacobiExpansion_overField_injective V hV D A G U F k
  have lin := ExpLin.expF_linear V hV D A G U F k
  let S₀ : ∀ α, SecA A F k → CompMod D F k α := fun α v => SecMod.mk _ (x v.sec α)
  have comb : ∀ (c : F) (v v' : SecA A F k) α, S₀ α (c • v + v') = c • S₀ α v + S₀ α v' := fun c v v' =>
    congrFun ((uq _ _ _ _ (hx (c • v + v').sec) (lin v.sec v'.sec (c • v + v').sec _ _
      (fun α => (c • S₀ α v + S₀ α v').sec) c (hx v.sec) (hx v'.sec) (fun _ => rfl) fun _ _ => rfl)).1 rfl)
  have z : ∀ α, S₀ α 0 = 0 := fun α => by
    have := comb 1 0 0 α
    rw [one_smul, one_smul, add_zero] at this
    exact left_eq_add.1 this
  refine ⟨fun α =>
    { toFun := S₀ α
      map_add' := fun v v' => by simpa only [one_smul] using comb 1 v v' α
      map_smul' := fun c v => by simpa only [add_zero, z, RingHom.id_apply] using comb c v 0 α },
    fun v s => ⟨fun h => (uq _ _ _ _ h (hx v.sec)).1 rfl, fun h => h ▸ hx v.sec⟩, fun v h => ?_⟩
  exact (uq _ _ _ _ (hx v.sec) (hx (0 : SecA A F k).sec)).2 (funext fun α => (h α).trans (z α).symm)

theorem exists_rep (hL : Laws) (hL₂ : Laws2) {R : Type} [CommRing R] [IsDomain R]
    (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [IsAlgClosed F]
    [Algebra (FractionRing R) F] {N : ℕ} (hN : (N : F) ≠ 0) :
    ∃ (Φ : TorsPt A (TFK (R := R) F) N → (SecA A F N ≃ₗ[F] SecA A F N))
      (e : TorsPt A (TFK (R := R) F) N → TorsPt A (TFK (R := R) F) N → Fˣ),
      Module.finrank F (SecA A F N) = N ^ A.g ∧ Nat.card (TorsPt A (TFK (R := R) F) N) = N ^ (2 * A.g) ∧
      (∀ a, ∃ θ : ThetaGrp A.A A.L N (TFK (R := R) F), θ.pt = a.1 ∧ ∀ v, IsActOf A.A A.L N θ v.sec (Φ a v).sec) ∧
      (∀ a b, ∃ c : Fˣ, ∀ v, Φ (a * b) v = (c : F) • Φ a (Φ b v)) ∧
      (∀ a b v, Φ a (Φ b v) = (e a b : F) • Φ b (Φ a v)) ∧ ∀ a, (∀ b, e a b = 1) → a = 1 := by
  obtain ⟨Φ, e, hd, h⟩ := exists_projective_rep hL hL₂ A (jFK (R := R) F) hN
  exact ⟨Φ, e, hd, (hL.mulN _ A N (Nat.pos_of_ne_zero fun e => hN (by rw [e, Nat.cast_zero]))).2.2.2.2 F
    (jFK (R := R) F) hN, h⟩

attribute [local instance] gtGroup

theorem exists_range {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (N : ℕ) {A : Type} [CommGroup A] (m : {g : GtPtF D F // GtTors D N g} → A)
    (minj : Function.Injective m) (madd : ∀ g g' g'', GtPtF.IsAdd g.1 g'.1 g''.1 → m g'' = m g * m g') :
    ∃ (H : Subgroup A) (a : TorChar D.X F N →* A), (∀ h, h ∈ H ↔ ∃ g, m g = h) ∧
      Nat.card H = Nat.card {g : GtPtF D F // GtTors D N g} ∧ Function.Injective a ∧
      ∀ τ, ∃ g, a τ = m g ∧ g.1 = torusPt D F (Additive.ofMul τ.1) := by
  let K := (nsmulAddMonoidHom N : GtPtF D F →+ GtPtF D F).ker
  let κ : K ≃ {g : GtPtF D F // GtTors D N g} := Equiv.subtypeEquivRight fun g => (GtCount.gtTors_iff N g).symm
  let ν : Multiplicative K →* A :=
    MonoidHom.mk' (fun g => m (κ g.toAdd)) fun g g' => madd _ _ _ ((isAdd_iff_eq _ _ _).2 rfl)
  have hν : Function.Injective ν := fun g g' h => κ.injective (minj h)
  let i : TorChar D.X F N →* Multiplicative K := MonoidHom.mk' (fun τ => Multiplicative.ofAdd
    ⟨torusPt D F (Additive.ofMul τ.1), show N • torusPt D F (Additive.ofMul τ.1) = 0 by
      rw [← map_nsmul, ← ofMul_pow, show τ.1 ^ N = 1 from τ.2, ofMul_one, map_zero]⟩)
    fun τ τ' => Subtype.ext (map_add (torusPt D F) (Additive.ofMul τ.1) (Additive.ofMul τ'.1))
  have iinj : Function.Injective i := fun τ τ' h =>
    Subtype.ext (Additive.ofMul.injective (torusPt_injective (congrArg Subtype.val h)))
  exact ⟨ν.range, ν.comp i, fun h => ⟨fun ⟨g, e⟩ => ⟨_, e⟩, fun ⟨g, e⟩ =>
      ⟨Multiplicative.ofAdd (κ.symm g), (congrArg m (κ.apply_symm_apply g)).trans e⟩⟩,
    (Nat.card_congr (MonoidHom.ofInjective hν).toEquiv).symm.trans (Nat.card_congr κ), hν.comp iinj,
    fun τ => ⟨κ (i τ).toAdd, rfl, rfl⟩⟩

theorem structure_of_acts (hL : Laws) (hL₂ : Laws2) {V : Type} [CommRing V] [IsDomain V] [IsNoetherianRing V] {I : Ideal V}
    {D : DegPre V} {A : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G : Over (Spec (CommRingCat.of V))} [GrpObj G]
    [IsCommMonObj G] (U : PreU I D A G) (hg : A.g = D.P.g + D.rank) (F : Type) [Field F] [IsAlgClosed F]
    [Algebra (FractionRing V) F] {N : ℕ} (hN : (N : F) ≠ 0) (S : ∀ α, SecA A F N →ₗ[F] CompMod D F N α)
    (hS : ∀ (v : SecA A F N) (s : Raw D F N), U.ExpF F N v.sec s ↔ s = fun α => (S α v).sec)
    (hS₀ : ∀ v, (∀ α, S α v = 0) → v = 0)
    (m : {g : GtPtF D F // GtTors D N g} → (TFK (R := V) F ⟶ A.A)) (minj : Function.Injective m)
    (mact : ∀ g, U.Acts F N 0 g.1 (m g)) (madd : ∀ g g' g'', GtPtF.IsAdd g.1 g'.1 g''.1 → m g'' = m g * m g') :
    ∃ Ψ : {g : GtPtF D F // GtTors D N g} → (SecA A F N ≃ₗ[F] SecA A F N), FiniteDimensional F (SecA A F N) ∧
      (∀ g : {g : GtPtF D F // GtTors D N g}, ∃ w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.1.b) (DegPre.lineε N)), w.IsGen ∧
        ∀ v : SecA A F N, PhiRaw D F N 0 g.1 w (fun α => (S α v).sec) fun α => (S α (Ψ g v)).sec) ∧
      ∀ α, (∀ v, ∃ v' ∈ classSub S N α, ∀ mu, S (α + N • mu) v' = S (α + N • mu) v) ∧
        Module.finrank F (classSub S N α) = N ^ D.P.g ∧
        ∀ W : Submodule F (SecA A F N), W ≤ classSub S N α → (∀ g, ∀ v ∈ W, Ψ g v ∈ W) →
          W = ⊥ ∨ W = classSub S N α := by
  have hN0 : N ≠ 0 := fun e => hN (by rw [e, Nat.cast_zero])
  have hN1 : 0 < N := Nat.pos_of_ne_zero hN0
  obtain ⟨Φ, e, hd, cA, hθ, hm, hc, hn⟩ := exists_rep hL hL₂ A F hN
  have : Finite (TorsPt A (TFK (R := V) F) N) :=
    Nat.finite_of_card_ne_zero (cA.trans_ne (pow_ne_zero _ hN0))
  have fd : FiniteDimensional F (SecA A F N) :=
    Module.finite_of_finrank_pos ((pow_pos hN1 _).trans_eq hd.symm)
  obtain ⟨m', hm'⟩ : ∃ m' : {g : GtPtF D F // GtTors D N g} → TorsPt A (TFK (R := V) F) N,
    ∀ g, (m' g).1 = m g := ⟨fun g => ⟨m g, (mact g).1⟩, fun _ => rfl⟩
  have hΨ : ∀ g : {g : GtPtF D F // GtTors D N g}, ∃ w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.1.b) (DegPre.lineε N)), w.IsGen ∧
      ∀ v : SecA A F N, PhiRaw D F N 0 g.1 w (fun α => (S α v).sec) fun α => (S α (Φ (m' g) v)).sec := fun g => by
    obtain ⟨θ, h₁, h₂⟩ := hθ (m' g)
    obtain ⟨w, hw, h⟩ := (mact g).2 θ (h₁.trans (hm' g))
    exact ⟨w, hw, fun v => h _ _ _ _ ((hS v _).2 rfl) ((hS _ _).2 rfl) (h₂ v)⟩
  obtain ⟨H, a, hH, cH, ainj, ha⟩ := exists_range D F N m'
    (fun g g' h => minj ((hm' g).symm.trans ((congrArg Subtype.val h).trans (hm' g'))))
    fun g g' g'' h => Subtype.ext ((hm' g'').trans ((madd g g' g'' h).trans
      (congrArg₂ (· * ·) (hm' g) (hm' g')).symm))
  have cT : Nat.card (TorChar D.X F N) = N ^ D.rank := GtCount.card_torus_torsion D.X F N hN
  rw [(GtCount.card_gtTors hL hL₂ V D F N hN).1] at cH
  have k₁ : ∀ τ, ∃ c : Fˣ, ∀ v α, S α (Φ (a τ) v) = ((c * evalChar F N α τ : Fˣ) : F) • S α v :=
    fun τ => by
      obtain ⟨g, e₁, e₂⟩ := ha τ
      obtain ⟨w, hw, h⟩ := hΨ g
      obtain ⟨c, hc⟩ := phiRaw_torus hL.globalFns τ.1 e₂ g.2 hw
      rw [e₁]
      exact ⟨c, fun v => hc (fun α => S α v) (fun α => S α (Φ (m' g) v)) (h v)⟩
  have k₂ : ∀ h ∈ H, ∀ α v v' (c : F), S α v = c • S α v' → S α (Φ h v) = c • S α (Φ h v') := by
    intro x hx β v v' c e
    obtain ⟨g, rfl⟩ := (hH x).1 hx
    obtain ⟨w, hw, h⟩ := hΨ g
    exact phiRaw_smul hL.globalFns g.2 hw (s := fun α => S α v) (s' := fun α => S α (Φ (m' g) v))
      (t := fun α => S α v') (t' := fun α => S α (Φ (m' g) v')) (h v) (h v') β c e
  refine ⟨fun g => Φ (m' g), fd, hΨ, fun α => ?_⟩
  obtain ⟨h₁, h₂, h₃⟩ := classSub_structure hN e Φ (by rw [cA, Nat.cast_pow]; exact pow_ne_zero _ hN)
    (by rw [cA, hd, mul_comm, pow_mul]) hm hc hn S hS₀ a ainj k₁ H k₂ (by rw [cT, cH, cA, hg]; ring) α
  refine ⟨h₁, ?_, fun W hW hst => h₃ W hW fun x hx => ?_⟩
  · refine Nat.eq_of_mul_eq_mul_right (pow_pos hN1 D.rank) ?_
    rw [← cT, h₂, cT, ← pow_add, ← hg, hd]
  · obtain ⟨g, rfl⟩ := (hH x).1 hx
    exact hst g

theorem weight_structure (hL : Laws) (hL₂ : Laws2) : AllPre fun {V} _ _ _ {D} {A} {_} _ _ U => ∀ N : ℕ, 1 ≤ N →
    ∃ (S : ∀ α, SecA A (Kbar V) N →ₗ[Kbar V] CompMod D (Kbar V) N α)
      (Ψ : {g : GtPtF D (Kbar V) // GtTors D N g} → (SecA A (Kbar V) N ≃ₗ[Kbar V] SecA A (Kbar V) N)),
      FiniteDimensional (Kbar V) (SecA A (Kbar V) N) ∧
      (∀ (v : SecA A (Kbar V) N) (s : Raw D (Kbar V) N), U.ExpF (Kbar V) N v.sec s ↔ s = fun α => (S α v).sec) ∧
      (∀ v, (∀ α, S α v = 0) → v = 0) ∧
      (∀ g : {g : GtPtF D (Kbar V) // GtTors D N g},
        ∃ w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D (Kbar V) g.1.b) (DegPre.lineε N)), w.IsGen ∧
        ∀ v : SecA A (Kbar V) N, PhiRaw D (Kbar V) N 0 g.1 w (fun α => (S α v).sec) fun α => (S α (Ψ g v)).sec) ∧
      ∀ α, (∀ v, ∃ v' ∈ classSub S N α, ∀ mu, S (α + N • mu) v' = S (α + N • mu) v) ∧
        Module.finrank (Kbar V) (classSub S N α) = N ^ D.P.g ∧
        ∀ W : Submodule (Kbar V) (SecA A (Kbar V) N), W ≤ classSub S N α → (∀ g, ∀ v ∈ W, Ψ g v ∈ W) →
          W = ⊥ ∨ W = classSub S N α := by
  intro V _ _ _ hV D A G _ _ U N hN1
  have : IsNoetherianRing V := by have := hV.1; infer_instance
  have hN : (N : Kbar V) ≠ 0 := by
    have := hV.2.2
    have : CharZero (FractionRing V) := inferInstance
    exact Nat.cast_ne_zero.2 (by omega)
  obtain ⟨S, hS, hS₀⟩ := exists_expansion hL hL₂ V hV D A G U (Kbar V) N hN1
  obtain ⟨m, minj, mact, madd⟩ := GlobalTheory.T.torusTorsion_to_abelianTorsion_theta_action hL hL₂ V hV D A G U N hN1
  obtain ⟨Ψ, fd, h⟩ := structure_of_acts hL hL₂ U (PreU.dim_eq V hV D A G U) (Kbar V) hN S hS hS₀ m minj mact madd
  exact ⟨S, Ψ, fd, hS, hS₀, h⟩

theorem main : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {_} _ _ U => ∀ N : ℕ, 1 ≤ N → (∀ (α : D.X) t s, U.ExpF (Kbar V) N t s → ∃ t' s', U.ExpF (Kbar V) N t' s' ∧ ∀ β, (∃ mu, β = α + N • mu) ∧ s' β = s β ∨ (¬ ∃ mu, β = α + N • mu) ∧ ∀ j, (s' β).f j = 0) ∧ (∀ α : D.X, ∃ mu, U.Supp (Kbar V) N (α + N • mu)) ∧ ∀ (α : D.X), U.Supp (Kbar V) N α → ∀ t s, U.ExpF (Kbar V) N t s → (∀ β, (¬ ∃ mu, β = α + N • mu) → ∀ j, (s β).f j = 0) → (∀ j, (s α).f j = 0) → ∀ j, t.f j = 0) := by
  intro hL hL₂ V _ _ _ hV D A G _ _ U N hN
  obtain ⟨S, Ψ, fd, hS, hS₀, hΨ, h⟩ := weight_structure hL hL₂ V hV D A G U N hN
  refine ⟨fun α t s hs => ?_, fun α => ?_, fun α ⟨t₀, s₀, h₀, j₀, hj₀⟩ t s hs hz hα => ?_⟩
  · obtain rfl := (hS (SecMod.mk _ t) s).1 hs
    obtain ⟨v', hv', e⟩ := (h α).1 (SecMod.mk _ t)
    refine ⟨v'.sec, _, (hS v' _).2 rfl, fun β => ?_⟩
    by_cases hβ : ∃ mu, β = α + N • mu
    · refine Or.inl ⟨hβ, ?_⟩
      obtain ⟨mu, rfl⟩ := hβ
      exact e mu
    · exact Or.inr ⟨hβ, (SecMod.eq_zero_iff_coord _).1 (hv' β hβ)⟩
  · have : Nontrivial (classSub S N α) :=
      Module.nontrivial_of_finrank_pos (R := Kbar V) ((pow_pos hN _).trans_eq (h α).2.1.symm)
    obtain ⟨v, hv⟩ := exists_ne (0 : classSub S N α)
    obtain ⟨β, hβ⟩ := not_forall.1 fun e => hv (Subtype.ext (hS₀ v.1 e))
    obtain ⟨mu, rfl⟩ := not_not.1 fun e => hβ (v.2 β e)
    exact ⟨mu, v.1.sec, _, (hS v.1 _).2 rfl, not_forall.1 fun e => hβ ((SecMod.eq_zero_iff_coord _).2 e)⟩
  · obtain rfl := (hS (SecMod.mk _ t) s).1 hs
    obtain rfl := (hS (SecMod.mk _ t₀) s₀).1 h₀
    have st : ∀ g β v, S β v = 0 → S β (Ψ g v) = 0 := fun g β v e => by
      obtain ⟨w, hw, hp⟩ := hΨ g
      exact (phiRaw_smul hL.globalFns g.2 hw (s := fun α => S α v) (s' := fun α => S α (Ψ g v))
        (t := fun α => S α v) (t' := fun α => S α (Ψ g v)) (hp v) (hp v) β 0 (e.trans (zero_smul _ _).symm)).trans (zero_smul _ _)
    rcases (h α).2.2 (classSub S N α ⊓ LinearMap.ker (S α)) inf_le_left
      (fun g v hv => ⟨fun β hβ => st g β v (hv.1 β hβ), st g α v hv.2⟩) with e | e
    · have : SecMod.mk _ t ∈ classSub S N α ⊓ LinearMap.ker (S α) :=
        ⟨fun β hβ => (SecMod.eq_zero_iff_coord _).2 (hz β hβ), (SecMod.eq_zero_iff_coord _).2 hα⟩
      rw [e] at this
      exact (SecMod.eq_zero_iff_coord _).1 ((Submodule.mem_bot _).1 this)
    · obtain ⟨v', hv', e'⟩ := (h α).1 (SecMod.mk _ t₀)
      have e₁ : ∀ β, β = α + N • (0 : D.X) → S β v' = S β (SecMod.mk _ t₀) := fun β hβ => hβ ▸ e' 0
      have e₂ : S α v' = 0 := (e.symm ▸ hv' : v' ∈ classSub S N α ⊓ LinearMap.ker (S α)).2
      exact absurd ((SecMod.eq_zero_iff_coord _).1 ((e₁ α (by rw [nsmul_zero, add_zero])).symm.trans e₂) j₀) hj₀

end GlobalTheory.UU.Weight
end
end

