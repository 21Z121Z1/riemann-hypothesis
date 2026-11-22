import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3315
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3311
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2486
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3147
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3313
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2893
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2897
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2729
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2772
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2774
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2773
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0183
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1353
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3310
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3312
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1961
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1797
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2829
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneFunctorBaseFunctorProperties
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu.Base

variable {p : ℕ} [Fact p.Prime] {P : ∀ (k : Type) [CommRing k], PDivGroup p k → Prop} (B : Base p P)
  {k : Type} [Field k] [CharP k p] [PerfectRing k p]

theorem map_id' {G : PDivGroup p k} (hG : P k G) : B.map hG hG (𝟙 G) = LinearMap.id :=
  LinearMap.ext fun m => B.smap_id G hG m

theorem map_comp' {G H K : PDivGroup p k} (hG : P k G) (hH : P k H) (hK : P k K) (f : G ⟶ H) (g : H ⟶ K) :
    B.map hG hK (f ≫ g) = B.map hG hH f ∘ₗ B.map hH hK g :=
  LinearMap.ext fun m => B.smap_comp hG hH hK (SemiHom.ofHom g) (SemiHom.ofHom f) (SemiHom.ofHom (f ≫ g))
    (fun _ _ => rfl) m

theorem map_add' {G H : PDivGroup p k} (hG : P k G) (hH : P k H) (f g : G ⟶ H) :
    B.map hG hH (f + g) = B.map hG hH f + B.map hG hH g :=
  LinearMap.ext fun m => B.smap_add hG hH f g m

def mapAdd {G H : PDivGroup p k} (hG : P k G) (hH : P k H) :
    (G ⟶ H) →+ (B.M H hH →ₗ[WittVector p k] B.M G hG) :=
  AddMonoidHom.mk' (B.map hG hH) (B.map_add' hG hH)

theorem map_zero' {G H : PDivGroup p k} (hG : P k G) (hH : P k H) : B.map hG hH (0 : G ⟶ H) = 0 :=
  map_zero (B.mapAdd hG hH)

theorem map_pow_smul {G H : PDivGroup p k} (hG : P k G) (hH : P k H) (n : ℕ) (f : G ⟶ H) (m : B.M H hH) :
    B.map hG hH ((p : ℤ_[p]) ^ n • f) m = p ^ n • B.map hG hH f m := by
  have e : (p : ℤ_[p]) ^ n • f = (p ^ n) • f := by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  have e2 : B.map hG hH ((p ^ n) • f) = (p ^ n) • B.map hG hH f := map_nsmul (B.mapAdd hG hH) _ _
  rw [e, e2, LinearMap.smul_apply]

theorem red_map {G H : PDivGroup p k} (hG : P k G) (hH : P k H) (f : G ⟶ H) (m : B.M H hH) :
    B.red G hG (B.map hG hH f m) = rigExtMap f (B.red H hH m) := by
  have := B.red_smap hG hH (SemiHom.ofHom f) m
  rw [SemiHom.ofHom_rig] at this
  exact this

theorem map_F {G H : PDivGroup p k} (hG : P k G) (hH : P k H) (f : G ⟶ H) (m : B.M H hH) :
    B.map hG hH f (B.F H hH m) = B.F G hG (B.map hG hH f m) := by
  let u := (SemiHom.ofHom f).comp (absFrob (p_eq_zero p k) H)
  have e1 : B.smap hG hH u m = B.map hG hH f (B.F H hH m) :=
    B.smap_comp hG hH hH (absFrob (p_eq_zero p k) H) (SemiHom.ofHom f) u (fun _ _ => rfl) m
  have e2 : B.smap hG hH u m = B.F G hG (B.map hG hH f m) :=
    B.smap_comp hG hG hH (SemiHom.ofHom f) (absFrob (p_eq_zero p k) G) u
      (fun n a => by simp only [u, SemiHom.comp_app, SemiHom.ofHom_app, absFrob_app, map_pow]) m
  exact e1.symm.trans e2

theorem finrank_M (G : PDivGroup p k) (hG : P k G) :
    Module.finrank (WittVector p k) (B.M G hG) = G.height := by
  haveI := B.free G hG
  haveI := B.finite G hG
  obtain ⟨_, h5⟩ := finrank_eq_of_semilinear_surjective (WittVector.constantCoeff_surjective p)
    (p_eq_zero p k) (B.red G hG) (B.red_surjective G hG) fun m => (B.red_eq_zero G hG m).1
  exact h5.symm.trans (rigExt_field_of_charP p k (p_eq_zero p k) G).2.1

theorem eq_zero_of_pow_smul {G : PDivGroup p k} (hG : P k G) (n : ℕ) (m : B.M G hG) (h : p ^ n • m = 0) :
    m = 0 := by
  haveI := B.free G hG
  rw [← Nat.cast_smul_eq_nsmul (WittVector p k)] at h
  refine (smul_eq_zero.1 h).resolve_left ?_
  rw [Nat.cast_pow]
  exact pow_ne_zero _ (WittVector.p_nonzero p k)

end GlobalTheory.Dieu.Base

namespace GlobalTheory.Dieu

theorem base_functor_props : ∀ (p : ℕ) [Fact p.Prime] (P : ∀ (k : Type) [CommRing k], PDivGroup p k → Prop) (B : Base p P) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H K : PDivGroup p k) (hG : P k G) (hH : P k H) (hK : P k K), B.map hG hG (𝟙 G) = LinearMap.id ∧ (∀ (f : G ⟶ H) (g : H ⟶ K), B.map hG hK (f ≫ g) = B.map hG hH f ∘ₗ B.map hH hK g) ∧ (∀ f g : G ⟶ H, B.map hG hH (f + g) = B.map hG hH f + B.map hG hH g) ∧ B.map hG hH (0 : G ⟶ H) = 0 ∧ (∀ (n : ℕ) (f : G ⟶ H) (m : B.M H hH), B.map hG hH ((p : ℤ_[p]) ^ n • f) m = p ^ n • B.map hG hH f m) ∧ (∀ (f : G ⟶ H) (m : B.M H hH), B.red G hG (B.map hG hH f m) = rigExtMap f (B.red H hH m)) ∧ (∀ (f : G ⟶ H) (m : B.M H hH), B.map hG hH f (B.F H hH m) = B.F G hG (B.map hG hH f m)) ∧ Module.finrank (WittVector p k) (B.M G hG) = G.height ∧ ∀ (n : ℕ) (m : B.M G hG), p ^ n • m = 0 → m = 0 := by
  intro p _ P B k _ _ _ G H K hG hH hK
  exact ⟨B.map_id' hG, fun f g => B.map_comp' hG hH hK f g, B.map_add' hG hH, B.map_zero' hG hH,
    B.map_pow_smul hG hH, B.red_map hG hH, B.map_F hG hH, B.finrank_M G hG, B.eq_zero_of_pow_smul hG⟩

end GlobalTheory.Dieu
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ThetaSetupGenericPointExists
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

noncomputable section

namespace GlobalTheory.Poinc.GSetup

open GlobalTheory.ThetaSysOfObj

theorem exists_big_ge (g n : ℕ) (hn : 2 ≤ n) (B : ℕ) : ∃ k j₁ : ℕ, 2 ≤ k ∧ B ≤ (n ^ k) ^ 2 ∧ 1 ≤ j₁ ∧ ∀ j ≥ j₁,
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω),
      S.g = g → S.N = (n ^ k) ^ 2 → S.r = n ^ j → S.Big := by
  have lt : ∀ m : ℕ, m < n ^ m := fun m => Nat.lt_pow_self hn
  obtain ⟨k₀, hk₀⟩ := exists_nat_gt (1 + 2 * (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2))
  set K := max k₀ B with hK
  set N := (n ^ (K + 2)) ^ 2 with hN
  have hN₁ : K + 2 < N := (lt _).trans_le (Nat.le_self_pow two_ne_zero _)
  obtain ⟨j₀, hj₀⟩ := exists_nat_gt
    (2 * ((N ^ g * g.factorial : ℕ) : ℝ) * ((g : ℝ) * (3 / 2 : ℝ) ^ g * (2 : ℝ) ^ ((g : ℝ) / 2 - 1)))
  refine ⟨K + 2, j₀ + 6 * (N ^ g * g.factorial) + 1, by omega, ?_, by omega, fun j hj o Ω _ _ _ S hg hS hr => ?_⟩
  · have : B ≤ K := le_max_right _ _
    omega
  have hj' := lt j
  unfold ThetaSys.Big
  rw [hg, hS, hr, ← hN]
  have hk₀K : k₀ ≤ K := le_max_left _ _
  refine ⟨hk₀.trans (by exact_mod_cast (by omega : k₀ < N)), ?_, ?_⟩
  · rw [Nat.cast_mul (n ^ j)]
    exact mul_lt_mul_of_pos_right (hj₀.trans (by exact_mod_cast (by omega : j₀ < n ^ j)))
      (by exact_mod_cast (by omega : 0 < N))
  · exact lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_right _ (by omega))

theorem exists_big_thetaSys_ge : ∀ (ℓ g : ℕ), ℓ.Prime → Odd ℓ → ∀ B : ℕ, ∃ k j₀ : ℕ, B ≤ (ℓ ^ k) ^ 2 ∧ ∀ j ≥ j₀, ∀ (o Ω : Type) [CommRing o]
    [Field Ω] [Algebra o Ω] [ArithBase o Ω] (R : Subalgebra o Ω) (J : Type) (b : TBase o ((ℓ ^ j) ^ 2))
    (u : TObj g ((ℓ ^ j) ^ 2) J b (spMap (algebraMap o R))) (w w' : J), R.FG → (∀ x : Ω, ∃ a ∈ R, ∃ c ∈ R, x = a / c) →
    u.Prim w w' → ∃ (S : ThetaSys o Ω) (ρ : S.Real) (hR : R ≤ S.R) (φ : ρ.P.A.left ⟶ u.A.left), S.Big ∧
      S.N = (ℓ ^ k) ^ 2 ∧ IsGrpPullback ρ.P.A u.A (spMap (Subalgebra.inclusion hR).toRingHom) φ ∧ LBIso ρ.P.L (u.L.pull φ) := by
  intro n g hn ho B
  obtain ⟨hL, hL₂⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨k, j₁, hk, hBk, hj₁, big⟩ := exists_big_ge g n hn.two_le B
  refine ⟨k, j₁ + 2 * k, hBk, fun j hj => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + k * 2 := ⟨j - k * 2, by omega⟩
  rw [pow_add, pow_mul]
  intro o Ω _ _ _ hb R J b u w₁ w₂ hR hΩ hpr
  have := u.ab.comm
  have : NeZero ((n ^ j * (n ^ k) ^ 2) ^ 2) := ⟨by have := hn.pos; positivity⟩
  have hS : ZH.HypS u.A u.L := ⟨u.act w₁, u.act w₂, u.hom w₁, u.hom w₂, hpr.1, hpr.2.2, hpr.2.1⟩
  have hun : IsUnit (n : o) := isUnit_of_dvd_unit (Nat.cast_dvd_cast
    (((dvd_pow_self n (by omega : j ≠ 0)).trans (dvd_mul_right _ _)).trans (dvd_pow_self _ two_ne_zero))) b.unit
  obtain ⟨lev, -⟩ := exists_level R u
  obtain ⟨S, ρ, h, φ, -, hN, hr, hg, hp, hlb, -⟩ :=
    GlobalTheory.ThetaReal.exists_thetaSys_real hL hL₂ o Ω R hR hΩ u.pol n k j b.ζ hn ho hk (by omega) hun hS lev
  exact ⟨S, ρ, h, φ, big j (by omega) o Ω S hg hN hr, hN, hp, hlb⟩

theorem exists_thetaSys_at : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ),
    IsE8 W → ∀ η ∈ genericPoints F.X, ∀ B : ℕ, ∃ (o₁ Ω₁ : Type) (_ : CommRing o₁) (_ : Field Ω₁) (_ : Algebra o₁ Ω₁)
      (_ : ArithBase o₁ Ω₁) (κ : cycAway n →+* o₁) (S : ThetaSys o₁ Ω₁) (ρ : S.Real) (u : Sp S.R ⟶ F.X),
      S.Big ∧ B ≤ S.N ∧ SharpOver F W ρ.P u ∧ (∀ w, (spMap S.R.val.toRingHom ≫ u) w = η) ∧
      spMap S.R.val.toRingHom ≫ u ≫ F.s = spMap ((algebraMap o₁ Ω₁).comp κ) ∧ κ.Finite ∧
      ((spMap S.R.val.toRingHom ≫ u).stalkMap (genericPoint (Sp Ω₁))).hom.Finite := by
  intro g n hg hn ho F W hW η hη B
  obtain ⟨ℓ, hℓ, hℓo, H⟩ := GlobalTheory.T.exists_chart_siegelLevelCover_sharpTheta g n hg hn ho F W hW η hη
  obtain ⟨k, j₀, hBk, Hs⟩ := exists_big_thetaSys_ge ℓ (8 * g) hℓ hℓo B
  obtain ⟨o, Ω, i₁, i₂, i₃, i₄, κ, R, J, b, t, w, w', x, hfg, hfr, hprim, hsh, hηx, hbase, hκ, hst⟩ :=
    H (max j₀ 1) (le_max_right _ _)
  obtain ⟨S, ρ, hR, φ, hbig, hN, hpb, hL⟩ := Hs (max j₀ 1) (le_max_left _ _) o Ω R J b t w w' hfg hfr hprim
  have ef : spMap S.R.val.toRingHom ≫ spMap (Subalgebra.inclusion hR).toRingHom = spMap R.val.toRingHom :=
    (Spec.map_comp (CommRingCat.ofHom (Subalgebra.inclusion hR).toRingHom) (CommRingCat.ofHom S.R.val.toRingHom)).symm
  refine ⟨o, Ω, i₁, i₂, i₃, i₄, κ, S, ρ, spMap (Subalgebra.inclusion hR).toRingHom ≫ x, hbig, hN ▸ hBk,
    hsh _ _ ρ.P φ hpb hL, ?_, ?_, hκ, ?_⟩
  · intro w
    rw [← Category.assoc, ef]
    exact hηx w
  · rw [Category.assoc, ← Category.assoc (spMap S.R.val.toRingHom), ef]
    exact hbase
  · rw [← Category.assoc, ef]
    exact hst

theorem exists_setup : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n))
    (i : F.X ⟶ Z), IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → IsOpenImmersion i → i ≫ z = F.s →
    Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i →
    ∀ η ∈ genericPoints F.X, ∀ B : ℕ, ∃ X₁ : Setup F W i, B ≤ X₁.S.N ∧ ∀ w, (spMap X₁.S.R.val.toRingHom ≫ X₁.u) w = η := by
  intro g n hg hn ho F Z z i hproj hZn hopen hiz hden W hW hT η hη B
  obtain ⟨o₁, Ω₁, _, _, _, _, κ, S, ρ, u, hbig, hB, hsharp, hgen, hbase, hκ, hstalk⟩ :=
    exists_thetaSys_at g n hg hn ho F W hW η hη B
  haveI : IsDedekindDomain (cycAway n) := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway _
  haveI : IsProper z := ((isProjOver_iff_isProper_and_exists_isAmpleLB z).1 hproj).1
  have hp : (spMap S.R.val.toRingHom ≫ u ≫ i) ≫ z = spMap ((algebraMap o₁ Ω₁).comp κ) := by
    simp only [Category.assoc, hiz]
    simpa only [Category.assoc] using hbase
  have hst : ((spMap S.R.val.toRingHom ≫ u ≫ i).stalkMap (genericPoint (Sp Ω₁))).hom.Finite := by
    rw [← Category.assoc, Scheme.Hom.stalkMap_comp]
    exact RingHom.Finite.comp hstalk (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (i.stalkMap _)).2)
  obtain ⟨M, π, hMn, hπ, hcomp⟩ := GlobalTheory.T.exists_normal_model_normalisation_dedekind (cycAway n) o₁ Ω₁ κ hκ Z z inferInstance inferInstance inferInstance
    (spMap S.R.val.toRingHom ≫ u ≫ i) hp hst
  exact ⟨Setup.mk o₁ Ω₁ S ρ hbig u hsharp (fun w => (hgen w).symm ▸ hη) M (GlobalTheory.IsNormalScheme.of_pred hMn) π hπ hcomp
    hg hn ho z hproj (GlobalTheory.IsNormalScheme.of_pred hZn) hopen hiz hden hW hT κ hbase, hB, hgen⟩

end GlobalTheory.Poinc.GSetup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqCounitOfHeightOneCotangentPullbackZero
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.HeightOneHom

theorem primitive_apply_mul {k C : Type} [Field k] [CommRing C] [HopfAlgebra k C]
    [IsCocomm k C] [Module.Finite k C] {φ : CartierDual k C} (hφ : cobOne k (CartierDual k C) φ = 0) (a b : C) :
    φ.ofConv (a * b) = counitAlgHom k C a • φ.ofConv b + counitAlgHom k C b • φ.ofConv a := by
  rw [cobOne_apply, sub_sub, sub_eq_zero, CartierDual.comul_eq_iff] at hφ
  have h := hφ a b
  rw [map_add, LinearMap.add_apply, CartierDual.pair_tmul_tmul, CartierDual.pair_tmul_tmul,
    CartierDual.one_apply, CartierDual.one_apply] at h
  change φ (a * b) = _
  rw [← h]
  simp only [counitAlgHom_apply, smul_eq_mul]
  ring

theorem eq_algebraMap_counit_of_cotMap_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    [CharP k p] (C : Type) [CommRing C] [HopfAlgebra k C] [IsCocomm k C] [Module.Finite k C]
    (D : Type) [CommRing D] [HopfAlgebra k D] [IsCocomm k D] [Module.Finite k D]
    (f : D →ₐc[k] C), (∀ a ∈ augIdeal k C, a ^ p = 0) → cotMap f = 0 →
    ∀ d, f d = algebraMap k C (counit (R := k) d) := by
  intro p _ k _ _ C _ _ _ _ D _ _ _ _ f hpow hcot d
  have hgen := GlobalTheory.HeightOneDual.adjoin_primitive_eq_top p k C hpow
  have hzero : ∀ φ : CartierDual k C, cobOne k (CartierDual k C) φ = 0 → ∀ x, φ (f x) = 0 := by
    intro φ hφ x
    have h1 := AugCot.lift_d (counitAlgHom k C) φ.ofConv (primitive_apply_mul hφ) (f x)
    have h2 : dUnit k (f x) = 0 := by
      rw [← cotMap_d f x, hcot, LinearMap.zero_apply]
    change φ.ofConv (f x) = 0
    rw [← h1]
    change AugCot.lift (counitAlgHom k C) φ.ofConv (primitive_apply_mul hφ) (dUnit k (f x)) = 0
    rw [h2, map_zero]
  have hone : ∀ φ : CartierDual k C, cobOne k (CartierDual k C) φ = 0 → φ 1 = 0 := by
    intro φ hφ
    have := AugCot.pointDer_algebraMap (primitive_apply_mul hφ) (1 : k)
    rwa [map_one] at this
  let T : CartierDual k C →ₐ[k] CartierDual k D :=
    (Algebra.ofId k _).comp (counitAlgHom k (CartierDual k C))
  have hT : ∀ φ : CartierDual k C, ∀ x : D, T φ x = φ 1 * counit (R := k) x := by
    intro φ x
    change (algebraMap k (CartierDual k D) (counit (R := k) φ)) x = _
    rw [Algebra.algebraMap_eq_smul_one, CartierDual.counit_apply]
    change φ 1 • (1 : CartierDual k D) x = _
    rw [CartierDual.one_apply, smul_eq_mul]
  have hM : (CartierDual.map f : CartierDual k C →ₐ[k] CartierDual k D) = T := by
    refine AlgHom.ext_of_adjoin_eq_top hgen fun φ hφ => ?_
    refine CartierDual.ext_apply fun x => ?_
    change CartierDual.map f φ x = T φ x
    rw [CartierDual.map_apply, hT, hzero φ hφ x, hone φ hφ, zero_mul]
  refine CartierDual.eq_of_forall_apply (R := k) fun φ => ?_
  have h1 : CartierDual.map f φ d = T φ d := by
    rw [← hM]; rfl
  rw [CartierDual.map_apply, hT] at h1
  rw [h1, Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul, mul_comm]

end GlobalTheory.HeightOneHom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionTraitUniformisingMumfordBun
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.exists_finExt_trait_unif_lam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (ρ : R →+* R₂), FinExt ρ ∧ ∀ (G₂ : Over (Sp R₂)) [GrpObj G₂] [IsCommMonObj G₂] (β : G₂.left ⟶ G.left) (β₂ : (G2 G₂).left ⟶ (G2 G).left), IsGrpPullback G₂ G (spMap ρ) β → Geo.Tor.IsSquare β β₂ → ∃ (A₂ : PolAV (Sp (FractionRing R₂))) (gen₂ : ((Over.pullback (jK R₂)).obj G₂) ≅ A₂.A) (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R₂ →+* W) (GW : Over (Sp W)) (_ : GrpObj GW) (_ : IsCommMonObj GW) (βW : GW.left ⟶ G₂.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW) (κ : pullback GW.hom (jK W) ⟶ pullback G₂.hom (jK R₂)), IsMonHom gen₂.hom ∧ ExtLam G₂ (A₂.L.pull gen₂.hom.left) (PP.pull β₂) ∧ GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ IsGrpPullback GW G₂ (spMap φ) βW ∧ κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ βW ∧ LBIso (UW.LG.L.pull (pullback.fst GW.hom (jK W))) ((A₂.L.pull gen₂.hom.left).pull κ) := by
  intro R _ _ _ hR G _ _ hG A gen hgen PP hPP
  obtain ⟨W, _, _, _, φ, GW, _, _, βW, βW₂, DW, AW, UW, hW, hφi, hφl, hpbW, hsqW, hlamW⟩ :=
    GlobalTheory.T.exists_trait_uniformisation_mumfordBundle R hR G hG A gen hgen PP hPP
  obtain ⟨ga, α, α₂, hga, hpbα, hsqα, hlamα, hcompα⟩ :=
    GlobalTheory.T.generic_uniformised_pullback_mumfordBundle_matching R hR G hG A gen hgen PP hPP W φ GW βW βW₂ DW AW UW hW hφi hφl hpbW hsqW hlamW

  have : CharZero R := hR.2
  have : CharZero (FractionRing R) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
  obtain ⟨K', _, io, Ω', _, j, l, A₁, α₁, α₁₂, p, hio, hlio, hpb₁, hsq₁, hlam₁, hp₁, hp₂, hpL⟩ :=
    GlobalTheory.T.exists_finite_extension_symmetric_bundle_descends (FractionRing R) (FractionRing W) ga A AW α α₂ hpbα hsqα hlamα
  have hcomp : ∀ r, l (io (algebraMap R _ r)) = j (algebraMap W _ (φ r)) := by
    intro r
    have h := DFunLike.congr_fun hlio (algebraMap R (FractionRing R) r)
    simp only [RingHom.comp_apply] at h
    rw [h, hga]
  obtain ⟨R₂, _, _, _, ρ, i, W₂, _, _, _, σ, φ₂, j₂, hρ, hW₂, hσ, hσl, hφ₂i, hφ₂l, hsq, hi, hj₂, hl₂⟩ :=
    GlobalTheory.T.exists_common_extension_dvr_fraction_fields R W hR hW φ hφi hφl K' Ω' io j l hio hcomp
  refine ⟨R₂, inferInstance, inferInstance, inferInstance, ρ, hρ, ?_⟩
  intro G₂ _ _ β β₂ hpb₂ hsq₂
  obtain ⟨A₂, gen₂, q, hgen₂, hext₂, hpbq, hlamq, hcompq⟩ :=
    GlobalTheory.T.transport_polarisedVariety_finiteExtension_fraction R G A gen hgen PP hPP K' io A₁ α₁ α₁₂ hpb₁ hsq₁ hlam₁ R₂ ρ i hρ.2.1 hi G₂ β β₂ hpb₂ hsq₂
  obtain ⟨GW', _, _, βW', τ, DW', AW', UW', κ, hpbW', hpbτ, hβτ, hκ, hLτ⟩ :=
    GlobalTheory.T.uniformisation_completeTrait_baseChange_finite_ext R R₂ W W₂ ρ φ σ φ₂ hR hW hW₂ hσ hσl hsq hφ₂i G hG G₂ β hpb₂ GW βW hpbW DW AW UW
  refine ⟨A₂, gen₂, W₂, inferInstance, inferInstance, inferInstance, φ₂, GW', inferInstance, inferInstance,
    βW', DW', AW', UW', κ, hgen₂, hext₂, hW₂, hφ₂i, hφ₂l, hpbW', hκ, ?_⟩
  exact GlobalTheory.T.uniformisation_bundle_genericFibre_descent R W R₂ W₂ K' Ω' φ ρ σ φ₂ io j l i j₂ hφi hρ.2.1 hσ.2.1 hφ₂i hsq hcomp hi hj₂ hl₂
    G A gen GW βW DW AW UW α hpbW hcompα A₁ α₁ p hpb₁ hp₁ hp₂ hpL G₂ β A₂ gen₂ q hpb₂ hpbq hlamq hcompq
    GW' βW' τ DW' AW' UW' κ hpbW' hpbτ hβτ hκ hLτ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorAlgebraisationReductions
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FormalAlg

theorem res_compat_of_gm {Z B : Scheme.{0}} {N : LB B} (b : Z ⟶ B) (s : ∀ i : N.ι, Γ(Z, b ⁻¹ᵁ N.U i)ˣ)
    (h : ∀ z i i', b z ∈ N.U i → b z ∈ N.U i' → gm (𝟙 _) z _ (s i) = gm b z _ (N.g i i') * gm (𝟙 _) z _ (s i'))
    (i i' : N.ι) :
    res (Scheme.Hom.preimage_mono b (inf_le_left : N.U i ⊓ N.U i' ≤ N.U i)) (s i) =
      pullU b _ (N.g i i') * res (Scheme.Hom.preimage_mono b (inf_le_right : N.U i ⊓ N.U i' ≤ N.U i')) (s i') := by
  apply unit_ext
  intro z hz
  have hz' : b z ∈ N.U i ⊓ N.U i' := hz
  rw [map_mul, gm_res _ z _ hz, gm_res _ z _ hz, gm_pull (𝟙 _) b z _ hz', Category.id_comp]
  exact h z i i' hz'.1 hz'.2

theorem appLE_eq_of_gm {Y Y' B : Scheme.{0}} {N : LB B} (β : Y ⟶ Y') (b : Y ⟶ B) (b' : Y' ⟶ B) (hβ : β ≫ b' = b)
    (i : N.ι) (s : Γ(Y, b ⁻¹ᵁ N.U i)ˣ) (s' : Γ(Y', b' ⁻¹ᵁ N.U i)ˣ)
    (h : ∀ z, b z ∈ N.U i → gm β z _ s' = gm (𝟙 _) z _ s) :
    (β.appLE (b' ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i) (by rw [← hβ]; exact le_rfl)).hom s'.val = s.val := by
  apply TopCat.Presheaf.section_ext Y.sheaf
  intro z hz
  have := congrArg Units.val (h z hz)
  have hz2 : β z ∈ b' ⁻¹ᵁ N.U i := by rw [← hβ] at hz; exact hz
  rw [gm_val β z _ hz2, gm_val (𝟙 Y) z _ hz] at this
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply]
  erw [TopCat.Presheaf.germ_res_apply]
  exact this

theorem exists_isGen_of_reductions : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (X : Over (Spec (CommRingCat.of R))), IsProper X.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ (N : LB X.left), N.IsLB → ∀ s : ∀ e (i : N.ι), Γ((Y e).left, b e ⁻¹ᵁ N.U i)ˣ, (∀ e z i i', b e z ∈ N.U i → b e z ∈ N.U i' → gm (𝟙 _) z _ (s e i) = gm (b e) z _ (N.g i i') * gm (𝟙 _) z _ (s e i')) → (∀ e z i, b e z ∈ N.U i → gm (β e) z _ (s (e + 1) i) = gm (𝟙 _) z _ (s e i)) → ∃ t : LB.Gen N, t.IsGen := by
  intro R _ _ I hI X hX Y β b hb hβ N hN s hs hsβ
  obtain ⟨G, q, u, hqa, hql, hu, hU⟩ := GlobalTheory.T.generatorScheme_lineBundle_affine_finiteType X.left N hN
  have hex := fun e => hU (Y e).left (b e) (s e) (res_compat_of_gm (b e) (s e) (fun z i i' => hs e z i i'))
  choose f hfq hfu using fun e => (hex e).exists
  have hfβ : ∀ e, β e ≫ f (e + 1) = f e := fun e =>
    (hex e).unique ⟨by rw [Category.assoc, hfq, hβ], fun i => by
        rw [← Scheme.Hom.appLE_comp_appLE (β e) (f (e + 1)) (q ⁻¹ᵁ N.U i) (b (e + 1) ⁻¹ᵁ N.U i) (b e ⁻¹ᵁ N.U i)
          (by rw [← hfq (e + 1)]; exact le_rfl) (by rw [← hβ e]; exact le_rfl),
          CommRingCat.comp_apply, hfu (e + 1) i]
        exact appLE_eq_of_gm (β e) (b e) (b (e + 1)) (hβ e) i (s e i) (s (e + 1) i) (hsβ e · i)⟩
      ⟨hfq e, hfu e⟩
  let Z : Over (Spec (CommRingCat.of R)) := Over.mk (q ≫ X.hom)
  have H := GlobalTheory.T.formalAlgebraisation_morphisms'
  obtain ⟨g, hg, -⟩ := H R I hI X Z hX (inferInstanceAs (IsSeparated (q ≫ X.hom)))
    (inferInstanceAs (LocallyOfFiniteType (q ≫ X.hom))) (inferInstanceAs (QuasiCompact (q ≫ X.hom)))
    Y β b hb hβ f (fun e => by
      show f e ≫ q ≫ X.hom = _
      rw [← Category.assoc, hfq, (hb e).w]) hfβ
  have hgq : g.left ≫ q = 𝟙 X.left := by
    have hH := H R I hI X X hX inferInstance inferInstance inferInstance Y β b hb hβ b (fun e => (hb e).w) hβ
    have h1 := hH.unique (y₁ := Over.homMk (g.left ≫ q) (by rw [Category.assoc]; exact Over.w g))
      (y₂ := 𝟙 X) (fun e => by
        show b e ≫ (g.left ≫ q) = b e
        rw [← Category.assoc, hg e, hfq e])
      (fun e => by rw [Over.id_left, Category.comp_id])
    exact congrArg CommaMorphism.left h1
  have hpt : ∀ x, q (g.left x) = x := fun x => by rw [← Scheme.Hom.comp_apply, hgq]; rfl
  have hle : ∀ i, N.U i ≤ g.left ⁻¹ᵁ (q ⁻¹ᵁ N.U i) := fun i x hx => by
    show q (g.left x) ∈ N.U i
    rw [hpt]; exact hx
  refine ⟨⟨fun i => res (hle i) (pullU g.left _ (u i))⟩, fun i j => ?_⟩
  apply unit_ext
  intro x hx
  have hx' : q (g.left x) ∈ N.U i ⊓ N.U j := by rw [hpt]; exact hx
  have key := congrArg (gm g.left x (q ⁻¹ᵁ (N.U i ⊓ N.U j))) (hu i j)
  rw [map_mul, gm_res _ x _ hx', gm_res _ x _ hx', gm_pull g.left q x _ hx', hgq] at key
  show gm (𝟙 _) x _ (res _ (res (hle i) (pullU g.left _ (u i)))) =
    gm (𝟙 _) x _ (N.g i j * res _ (res (hle j) (pullU g.left _ (u j))))
  rw [map_mul, gm_res _ x _ hx, gm_res _ x _ hx.1, gm_res _ x _ hx, gm_res _ x _ hx.2,
    gm_pull (𝟙 _) g.left x _ (hle i hx.1), gm_pull (𝟙 _) g.left x _ (hle j hx.2),
    Category.id_comp]
  exact key

end GlobalTheory.FormalAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGridDatumPureTensorVacuaAE
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.SmallDatumVac

theorem exists_datum_pure_vac : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j))
    (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j)))
    (e : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Num G i j) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsTripleOf W M t i j e Bs Γ X) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om')
    (hv : ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ Bs.v₁),
    ∃ ΦB, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsDatumB W e Γ Θ' ΦB ∧
      ∃ (m : ℕ) (f : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank)))
        (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F, (Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank) → Fv D.host.F v) → ℂ)
        (φ₀ : (Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank) → Fv D.host.F Bs.v₁) → ℂ),
        ΦB = ∑ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f k) (φ k) ∧ (∀ k v, φ k v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ k, ∀ᶠ v in Filter.cofinite, φ k v = Γ.M'.vac v) ∧
        (∀ k, φ k Bs.v₁ = φ₀) ∧ φ₀ ∈ GlobalTheory.WeilM.SB _ ∧ φ₀ ≠ 0 ∧
        ∃ (L₁ : Submodule (𝓞 D.host.E) (Fin (G.V (.grid i j)).rank → D.host.E)) (L₂ : Submodule (𝓞 D.host.E) (Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank) → D.host.E))
          (θ : 𝓞 D.host.E), (θ : D.host.E) + D.sp.cm.sig θ = 1 ∧ (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) φ₀
            (Bs.ψ (⅟(2 : AF D.host.F) * symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
              (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) • φ₀)) ∧
          ∀ ψ₀ ∈ GlobalTheory.WeilM.SB (Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank) → Fv D.host.F Bs.v₁), (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) ψ₀
            (Bs.ψ (⅟(2 : AF D.host.F) * symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
              (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) • ψ₀)) → ∃ c : ℂ, ψ₀ = c • φ₀ := by
  intro D T L sc G μ₀ hL W B ρ t i j M hM Θ Θ' hΘ g₁ e Bs Γ X om om' h hTr hv
  obtain ⟨ΦB, hD, m, f, φ, φ₀, hsum, hSB, hvac, hv1, h0SB, h0ne, L₁, L₂, θ, hL1, hL2, hSD, hθ, hfix⟩ :=
    GlobalTheory.T.exists_pureTensorSum_datum_routeThroughSmallVertex hL W B ρ t i j M hM Θ Θ' hΘ e Bs Γ X om om' h hTr hv
  have hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PsiUnr Bs.ψ Bs.v₁ := h.ψ ▸ GlobalTheory.T.localAddCharUnramified_of_splitsCompletelyAbovePlace W Bs.v₁ hTr.chars.good.2
  exact ⟨ΦB, hD, m, f, φ, φ₀, hsum, hSB, hvac, hv1, h0SB, h0ne, L₁, L₂, θ, hθ, hfix,
    fun ψ₀ hψ₀ hfix' => GlobalTheory.T.heisenbergLatticeVacuum_unique_up_to_scalar Bs Γ Bs.v₁ L₁ L₂ θ hψ hL1 hL2 hSD hθ φ₀ ψ₀ h0SB h0ne hfix hψ₀ hfix'⟩

end GlobalTheory.SmallDatumVac
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalRepresentingSchemeHomFixedPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_representing_scheme_homFixedPullback : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → Out.RelAmple A L → Out.RelAmple B M → ∀ p : Sp Rg, ∃ U : (Sp Rg).Opens, p ∈ U ∧ ∃ (AU : Over (U).toScheme) (_ : GrpObj AU) (BU : Over (U).toScheme) (_ : GrpObj BU) (φA : AU.left ⟶ A.left) (φB : BU.left ⟶ B.left), IsGrpPullback AU A (U).ι φA ∧ IsGrpPullback BU B (U).ι φB ∧ ∃ R : HomFixRep AU BU (L.pull φA) (M.pull φB), QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  first | (exact @GlobalTheory.HomFixLocal.exists_local_homFixRep) | (exact GlobalTheory.HomFixLocal.exists_local_homFixRep) | (intros; apply GlobalTheory.HomFixLocal.exists_local_homFixRep  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSectionThetaQuotientProjChartStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localSection_thetaQuotient_projChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k Ω : Type) [CommRing k]
    [IsNoetherianRing k] [Field Ω] [CharZero Ω] [Algebra k Ω] (M : RatModel k Ω) (t : SAB H M.Z) (g m n : ℕ)
    (c : Fin (n + 1) → Ω) (h : M.Z ⟶ PSpace k n) (θ : SecAt t.G t.PP.L M.pt) (pt : Fin (n + 1) → (Over.mk M.pt ⟶ t.G)),
    Geo.Tor.IsNormalScheme M.Z → Odd m → 3 ≤ m → IsUnit (m : k) → PolFib t.G t.PP.L g M.pt →
    IsGenSec t.G t.PP.L _ θ → ThList t.G t.PP.L t.PP.rig m M.pt θ pt c → PCrd (M.pt ≫ h) c →
    ∀ (a : Fin (n + 1)) (z : M.Z), z ∈ h ⁻¹ᵁ chart k n a → ∃ N : M.Z.Opens, z ∈ N ∧ N ≤ h ⁻¹ᵁ chart k n a ∧
      ∃ s : LocSec t.G t.PP.L N, IsLocSec s ∧
        GenIs M.pt s ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a)⁻¹ • SecM.ofSec t.G θ) ∧ FibNz s N := by
  first | exact @GlobalTheory.UMin.ThBdl.exists_locSec_theta_chart | exact GlobalTheory.UMin.ThBdl.exists_locSec_theta_chart | (intros; apply GlobalTheory.UMin.ThBdl.exists_locSec_theta_chart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonicRatCharPolyAbelianVarietyStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_monic_rat_charPoly_abelianVariety : ∀ (K : Type) [Field K] (A : AbVar K) (f : End A), ∃ P : Polynomial ℚ, P.Monic ∧ P.natDegree = 2 * A.dim ∧ ∀ n : ℤ, P.eval (n : ℚ) = (deg (A := A) (B := A) ((n : End A) - f) : ℚ) := by
  first | (exact @GlobalTheory.charPolyRat) | (exact GlobalTheory.charPolyRat) | (intros; apply GlobalTheory.charPolyRat  <;> assumption)
end

