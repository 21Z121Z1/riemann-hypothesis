import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0406
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0438
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2458
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2295
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2520
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0074
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0316
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0134
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAlgAtlasAtlasOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0218
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0124
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2459
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleMemRangeCobOfPullbackMulByPow
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace PDivGroup

variable {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)

theorem exists_injective_mulBy_pow_eq_comp_resOne (n : ℕ) : ∃ q : G.A 1 →ₐc[R] G.A (n + 1),
    Function.Injective q ∧ ∀ a, mulBy R _ (p ^ n) a = q (G.resOne n a) := by
  induction n with
  | zero =>
    refine ⟨BialgHom.id R _, Function.injective_id, fun a => ?_⟩
    rw [pow_zero, mulBy, pow_one]
    rfl
  | succ n ih =>
    obtain ⟨q, hq, hq'⟩ := ih
    refine ⟨(G.mulP (n + 1)).comp q, (Test.mulP_injective G (n + 1)).comp hq, fun a => ?_⟩
    rw [pow_succ', ← mulBy_mulBy, ← mulP_res, map_mulBy, hq']
    rfl

theorem mulBy_pow_zero_eq_id (n : ℕ) : mulBy R (G.A n) (p ^ 0) = BialgHom.id R _ := by
  rw [pow_zero, mulBy, pow_one]

theorem exists_cob_eq_mulBy_eq (c : G.cocycles) (B : G.funs)
    (hB : ∀ n, cobOne R _ (B.1 n) = pullbackTwo (mulBy R (G.A n) p) (c.1 n)) (h1 : B.1 1 = 0) :
    ∃ e : G.funs, G.cob e = c ∧ ∀ n, mulBy R _ p (e.1 n) = B.1 n := by
  have hlev : ∀ n, cobOne R _ (B.1 (n + 1)) = pullbackTwo (G.mulP n) (c.1 n) := by
    intro n
    rw [hB, ← mulP_comp_res, pullTwo_comp, (c.2 n).2]
  have hinv : ∀ n, G.transl n (B.1 (n + 1)) = B.1 (n + 1) ⊗ₜ 1 := fun n =>
    G.transl_eq_of_cobOne_eq_pullTwo n _ _ (hlev n) (by rw [resOne_funs, h1])
  choose e he using fun n => G.exists_mulP_eq_of_transl_eq n (B.1 (n + 1)) (hinv n)
  have hres : ∀ n, G.res n (e (n + 1)) = e n := by
    intro n
    apply Test.mulP_injective G n
    rw [mulP_res, he n, ← B.2 (n + 1), ← he (n + 1), res_mulP]
  refine ⟨⟨e, hres⟩, Subtype.ext (funext fun n => ?_), fun n => ?_⟩
  · change cobOne R _ (e n) = c.1 n
    apply G.pullbackTwo_mulP_injective n
    rw [pullTwo_cobOne, he n, hlev n]
  · change mulBy R _ p (e n) = B.1 n
    rw [← res_mulP, he n, B.2 n]

theorem exists_cob_eq_mulBy_pow_eq [Fact p.Prime] (N : ℕ) : ∀ (c : G.cocycles) (B : G.funs),
    (∀ n, cobOne R _ (B.1 n) = pullbackTwo (mulBy R (G.A n) (p ^ N)) (c.1 n)) → B.1 N = 0 →
      ∃ e : G.funs, G.cob e = c ∧ ∀ n, mulBy R _ (p ^ N) (e.1 n) = B.1 n := by
  induction N with
  | zero =>
    intro c B hB _
    refine ⟨B, Subtype.ext (funext fun n => ?_), fun n => ?_⟩
    · change cobOne R _ (B.1 n) = c.1 n
      rw [hB n, mulBy_pow_zero_eq_id, pullTwo_id]
    · rw [mulBy_pow_zero_eq_id]
      rfl
  | succ N ih =>
    intro c B hB hN
    let c' : G.cocycles := cocyclesMap ((p : ℤ_[p]) • 𝟙 G) c
    have hc' : ∀ n, c'.1 n = pullbackTwo (mulBy R (G.A n) p) (c.1 n) := fun n => by
      change pullbackTwo (Hom.app ((p : ℤ_[p]) • 𝟙 G) n) (c.1 n) = _
      rw [natCast_smul_id_app]
    have hB' : ∀ n, cobOne R _ (B.1 n) = pullbackTwo (mulBy R (G.A n) (p ^ N)) (c'.1 n) := fun n => by
      rw [hB n, hc' n, ← pullTwo_comp, pow_succ,
        show (mulBy R (G.A n) (p ^ N)).comp (mulBy R _ p) = mulBy R _ (p ^ N * p) from
          BialgHom.ext fun a => mulBy_mulBy _ _ a]
    obtain ⟨e', he', hm'⟩ := ih c' B hB' ((B.2 N).symm.trans (by rw [hN, map_zero]))
    have h1 : e'.1 1 = 0 := by
      obtain ⟨q, hq, hq'⟩ := G.exists_injective_mulBy_pow_eq_comp_resOne N
      apply hq
      rw [map_zero, ← G.resOne_funs e' N, ← hq', hm', hN]
    have hA : ∀ n, cobOne R _ (e'.1 n) = pullbackTwo (mulBy R (G.A n) p) (c.1 n) := fun n =>
      (congrArg (fun d : G.cocycles => d.1 n) he').trans (hc' n)
    obtain ⟨e, he, hm⟩ := G.exists_cob_eq_mulBy_eq c e' hA h1
    refine ⟨e, he, fun n => ?_⟩
    rw [pow_succ, ← mulBy_mulBy, hm, hm']

end PDivGroup

theorem cocycle_mem_range_cob_of_pullback_mulBy_pow :
    ∀ (p : ℕ) [Fact p.Prime]  (R : Type) [CommRing R] (G : PDivGroup p R) (N : ℕ) (c : G.cocycles)
      (B : ∀ n, G.A n), (∀ n, G.res n (B (n + 1)) = B n) →
      (∀ n, cobOne R (G.A n) (B n) = pullbackTwo (mulBy R (G.A n) (p ^ N)) (c.1 n)) → B N = 0 →
        c ∈ LinearMap.range G.cob := by
  intro p _ R _ G N c B hB hc hN
  obtain ⟨e, he, -⟩ := G.exists_cob_eq_mulBy_pow_eq N c ⟨B, hB⟩ hc hN
  exact ⟨e, he⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightAndMultiplicityPullbackIsIsoOpenStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coheight_and_multiplicity_pullback_isIso_open : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) [IsDominant s] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (U : X.Opens), IsIso (s ∣_ U) → ∀ w : Y, s w ∈ U → Order.coheight w = Order.coheight (s w) ∧ ∀ D : CartierDiv X, (pullCart s D).mult w = D.mult (s w) := by
  first | exact @GlobalTheory.Discrepancy.MultIso.coheight_eq_and_mult_pullCart | exact GlobalTheory.Discrepancy.MultIso.coheight_eq_and_mult_pullCart | (intros; apply GlobalTheory.Discrepancy.MultIso.coheight_eq_and_mult_pullCart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSec
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.VB

namespace GlobalTheory.FlagZ.Taut

variable (ι : Type) [Fintype ι] (N : ℕ)

abbrev stdE : (Sp ℤ).Modules := (HermVB.std (𝟙 (Sp ℤ)) N).E

variable {N} in

def colSec {A : Type} [CommRing A] (x : Sp A ⟶ Sp ℤ) (g : Matrix (Fin N) (Fin N) A) (j : Fin N) :
    Γ((Scheme.Modules.pullback x).obj (stdE N), ⊤) :=
  ∑ i, (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (g i j) •
    GlobalTheory.QCoh.pullbackSections x (stdE N) (by simp) (freeFrame (Sp ℤ) (Fin N) i)

def IsTaut (fl : ∀ _ : ι, Vert.Flag ((Scheme.Modules.pullback (flStr ι N)).obj (stdE N)) N) : Prop :=
  ∀ (A : Type) [CommRing A] (g : ι → GL (Fin N) A) (a : ι) (l : Fin (N + 1)),
    ∃ s : Fin l → Γ((Scheme.Modules.pullback (flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g)).obj ((fl a).F l), ⊤),
      IsFrame s ∧ ∀ j, ((Scheme.Modules.pullback (flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g)).map ((fl a).ι l) ≫
        (Scheme.Modules.pullbackComp (flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g) (flStr ι N)).hom.app
          (stdE N)).app ⊤ (s j) =
        colSec (flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g ≫ flStr ι N) (g a).1 (Fin.castLE l.is_le j)

end GlobalTheory.FlagZ.Taut
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRefinementOfCoverAndModel
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm
open CategoryTheory.Limits TopologicalSpace

namespace GlobalTheory.Mean4O.CoverDom

theorem isNormalScheme_G {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y) : GlobalTheory.IsNormalScheme V.G := by
  have : GlobalTheory.IsNormalScheme V.X := GlobalTheory.IsNormalScheme.of_pred V.normal
  have : Flat (spMap (algebraMap (𝓞 F) F)) := flat_specMap_localization (nonZeroDivisors (𝓞 F)) F
  have : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) :=
    IsPreimmersion.of_isLocalization (R := 𝓞 F) (S := F) (nonZeroDivisors (𝓞 F))
  have : Flat V.j := MorphismProperty.of_isPullback V.pb.flip ‹_›
  have : IsPreimmersion V.j := MorphismProperty.of_isPullback V.pb.flip ‹_›
  have : ∀ x, IsIso (V.j.stalkMap x) := fun x => isIso_stalkMap_of_flat_of_surjectiveOnStalks V.j x
  exact GlobalTheory.IsNormalScheme.of_isIso_stalkMap V.j

theorem exists_cover_dominating (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y)
    (M : TrueGeo.Model Y) : ∃ (V' : Cover Y) (a : V'.X ⟶ V.X) (g : V'.G ⟶ V.G) (b : V'.X ⟶ M.X),
      a ≫ V.p = V'.p ∧ b ≫ M.p = V'.p ∧ V'.j ≫ a = g ≫ V.j ∧ g ≫ V.π = V'.π ∧
      g (genericPoint V'.G) = genericPoint V.G ∧ V'.j ≫ b = V'.π ≫ M.j := by
  have H₀ := V.pb
  have := M.ar.isIntegral
  have := V.ar.isLocallyNoetherian
  have : IsProper V.p := CommonModel.isProper_of_isProjOver V.ar.isProjOver
  have : IsProper M.p := CommonModel.isProper_of_isProjOver M.ar.isProjOver
  let r := pullback.fst V.p M.p
  have hc : V.j ≫ V.p = (V.π ≫ M.j) ≫ M.p := by
    rw [V.pb.w, Category.assoc, Category.assoc, M.pb.w]
  let h : V.G ⟶ pullback V.p M.p := pullback.lift V.j (V.π ≫ M.j) hc
  have hr : h ≫ r = V.j := pullback.lift_fst _ _ _
  have hr' : h ≫ pullback.snd V.p M.p = V.π ≫ M.j := pullback.lift_snd _ _ _
  have hW : IsProjOver (r ≫ V.p) := GlobalTheory.ProjSpace.isProjOver_pullback V.ar.isProjOver M.ar.isProjOver
  have w : h ≫ r ≫ V.p = (V.π ≫ Y.str) ≫ spMap (algebraMap (𝓞 F) F) := by
    rw [← Category.assoc, hr, H₀.w]
  have hb := IsPullback.of_hasPullback (r ≫ V.p) (spMap (algebraMap (𝓞 F) F))
  let f' : V.G ⟶ pullback (r ≫ V.p) (spMap (algebraMap (𝓞 F) F)) := pullback.lift h (V.π ≫ Y.str) w
  let ρ : pullback (r ≫ V.p) (spMap (algebraMap (𝓞 F) F)) ⟶ V.G :=
    H₀.lift (pullback.fst _ _ ≫ r) (pullback.snd _ _) (by rw [Category.assoc]; exact hb.w)
  have hρ : ρ ≫ V.π ≫ Y.str = pullback.snd _ _ := H₀.lift_snd _ _ _
  have hfρ : f' ≫ ρ = 𝟙 V.G := by
    apply H₀.hom_ext
    · rw [Category.assoc, H₀.lift_fst, pullback.lift_fst_assoc, hr, Category.id_comp]
    · rw [Category.assoc, hρ, pullback.lift_snd, Category.id_comp]
  have : IsSeparated (ρ ≫ V.π ≫ Y.str) := by rw [hρ]; infer_instance
  have : IsSeparated ρ := IsSeparated.of_comp ρ (V.π ≫ Y.str)
  have : IsClosedImmersion (f' ≫ ρ) := by rw [hfρ]; infer_instance
  have : IsClosedImmersion f' := IsClosedImmersion.of_comp f' ρ
  have hh : h = f' ≫ 𝟙 _ ≫ pullback.fst _ _ := by rw [Category.id_comp, pullback.lift_fst]
  have : IsAffineHom (pullback.fst (r ≫ V.p) (spMap (algebraMap (𝓞 F) F))) :=
    MorphismProperty.of_isPullback hb.flip (isAffineHom_of_isAffine _)
  have : IsAffineHom h := by rw [hh]; infer_instance
  have hpb := GlobalTheory.isPullback_toNormalization_of_isLocalization (nonZeroDivisors (𝓞 F)) hb f' (𝟙 _) h hh
  rw [Category.id_comp] at hpb
  have hfin : IsFinite h.fromNormalization :=
    GlobalTheory.isFinite_fromNormalization_of_over_fractionRing (o := .of (𝓞 F)) h (r ≫ V.p) F (V.π ≫ Y.str) w
  have : GlobalTheory.IsNormalScheme V.G := isNormalScheme_G V
  have : GlobalTheory.IsNormalScheme h.normalization := GlobalTheory.IsNormalScheme.normalization_of_isIntegral h
  have hint : IsIntegral h.normalization := inferInstance
  have : Flat (spMap (algebraMap (𝓞 F) F)) := flat_specMap_localization (nonZeroDivisors (𝓞 F)) F
  have : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) :=
    IsPreimmersion.of_isLocalization (R := 𝓞 F) (S := F) (nonZeroDivisors (𝓞 F))
  have : Flat V.j := MorphismProperty.of_isPullback V.pb.flip ‹_›
  have : IsPreimmersion V.j := MorphismProperty.of_isPullback V.pb.flip ‹_›
  have e₁ : h.toNormalization ≫ h.fromNormalization ≫ r = V.j := by
    rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hr]
  have e₂ : h.toNormalization ≫ h.fromNormalization ≫ pullback.snd V.p M.p = V.π ≫ M.j := by
    rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hr']
  have hU := ModelDom.exists_isIso_restrict h.toNormalization (h.fromNormalization ≫ r) V.j e₁
  have hdim : topologicalKrullDim h.normalization = (Y.dim + 1 : ℕ) := by
    obtain ⟨U, hne, _⟩ := hU
    obtain ⟨_, _⟩ := birational_of_isIso_morphismRestrict (h.fromNormalization ≫ r) U hne.to_subtype
    have := surjective_of_isDominant_of_isClosed_range (h.fromNormalization ≫ r)
      (h.fromNormalization ≫ r).isClosedMap.isClosed_range
    rw [← V.ar.dim_eq]
    exact (ModelDom.dim_le_of_birational (h.fromNormalization ≫ r)).antisymm
      (PosBaseChange.dim_le_of_isClosedMap (h.fromNormalization ≫ r).isClosedMap
        (h.fromNormalization ≫ r).surjective)
  have hfl : Flat (h.fromNormalization ≫ r ≫ V.p) := GlobalTheory.flat_fromNormalization_comp h F (r ≫ V.p) (V.π ≫ Y.str) w
  have hfZ : Flat (spMap (Int.castRingHom (𝓞 F))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat ℤ (𝓞 F))
  have hpb' := hpb.paste_vert hb
  rw [pullback.lift_snd] at hpb'
  let V' : Cover Y :=
    { X := h.normalization
      p := h.fromNormalization ≫ r ≫ V.p
      ar := ⟨V.ar.isDomain, V.ar.finite, hint, GlobalTheory.isProjOver_comp_of_finite _ _ _ _ _ hfin hW, inferInstance, hdim⟩
      normal := GlobalTheory.IsNormalScheme.pred _
      G := V.G
      j := h.toNormalization
      π := V.π
      pb := hpb'
      φ := V.φ
      φ_spec := V.φ_spec }
  refine ⟨V', h.fromNormalization ≫ r, 𝟙 V.G, h.fromNormalization ≫ pullback.snd V.p M.p, Category.assoc _ _ _, ?_,
    e₁.trans (Category.id_comp _).symm, Category.id_comp _, rfl, e₂⟩
  change (h.fromNormalization ≫ pullback.snd V.p M.p) ≫ M.p = h.fromNormalization ≫ r ≫ V.p
  rw [Category.assoc, ← pullback.condition]

end GlobalTheory.Mean4O.CoverDom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingSpreadPointsEqSpreadRoot
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumPair

theorem weilIs_of_spread : ∀ (Ω T : Type) [Field Ω] [CommRing T] [IsDomain T] [IsNoetherianRing T] (jT : T →+* Ω), Function.Injective jT → ∀ (A : PolAV (Sp Ω)) (P : PolAV (Sp T)) (φ : A.A.left ⟶ P.A.left), IsGrpPullback A.A P.A (spMap jT) φ → LBIso A.L (P.L.pull φ) → ∀ (k : ℕ) (x x' : baseOver (Sp Ω) ⟶ A.A) (y y' : baseOver (Sp T) ⟶ P.A) (c : Tˣ), 1 ≤ k → x.left ≫ φ = spMap jT ≫ y.left → x'.left ≫ φ = spMap jT ≫ y'.left → y ^ k = 1 → y' ^ k = 1 → WeilIs A.A A.L k x x' (unitOn (Units.map jT.toMonoidHom c)) → WeilIs P.A P.L k y y' (unitOn c) := by
  intro Ω T _ _ _ _ jT hj A P φ hp hw k x x' y y' c hk hx hx' hy hy' hW
  obtain ⟨⟨hL, -⟩, -⟩ := GlobalTheory.lawsAndExpansions
  haveI : IsCommMonObj A.A := A.isAb.comm
  haveI : IsLocallyNoetherian (Sp T) := inferInstance
  haveI : IsLocallyNoetherian (Sp Ω) := inferInstance
  obtain ⟨c₀, hc₀, -⟩ := (hL.weil (Sp T) P k (baseOver _)).1 y y' hy hy'
  let h : Over.mk ((baseOver (Sp Ω)).hom ≫ spMap jT) ⟶ baseOver (Sp T) := Over.homMk (spMap jT) (by simp)
  have H1 := GlobalTheory.CommPairing.weilIs_pull hL.globalFns P.isAb P.isLB h hc₀
  have H2 := (GlobalTheory.weilIs_grpPullback_of_comm' (Sp T) (Sp Ω) P.A A.A (spMap jT) φ P.L A.L P.isLB A.isLB hp hw
    (baseOver (Sp Ω)) k x x' (h ≫ y) (h ≫ y') _ hx.symm hx'.symm).2 H1
  have inj : ∀ a b : baseOver (Sp Ω) ⟶ A.A, a.left ≫ φ = b.left ≫ φ → a = b := by
    intro a b e
    apply Over.OverMorphism.ext
    apply hp.1.hom_ext e
    rw [Over.w, Over.w]
  have tors : ∀ (a : baseOver (Sp Ω) ⟶ A.A) (b : baseOver (Sp T) ⟶ P.A), a.left ≫ φ = spMap jT ≫ b.left →
      b ^ k = 1 → a ^ k = 1 := by
    intro a b e hb
    apply inj
    have e1 : (ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushHom hp (baseOver (Sp Ω)) (a ^ k)) = (h ≫ b) ^ k := by
      rw [map_pow]
      congr 1
      exact Over.OverMorphism.ext e
    have e2 : (ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushHom hp (baseOver (Sp Ω)) 1) = (h ≫ b) ^ k := by
      rw [map_one, ← MonObj.comp_pow, hb, MonObj.comp_one]
    exact (congrArg (fun z => z.left) e1).trans (congrArg (fun z => z.left) e2).symm
  have hxk := tors x y hx hy
  have hxk' := tors x' y' hx' hy'
  have U := (hL.weil (Sp Ω) A k (baseOver _)).1 x x' hxk hxk'
  have e3 := U.unique H2 hW
  have nat : ∀ a : T, (spMap jT).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom a) =
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (jT a) := by
    intro a
    have := congrArg (fun f => f.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom jT))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    exact this.symm
  have ginj : Function.Injective (spMap jT).appTop.hom := by
    intro a b e
    have ea : a = (Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of T)).hom.hom a) := by
      simp
    have eb : b = (Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of T)).hom.hom b) := by
      simp
    rw [ea, eb, nat, nat] at e
    have e' := congrArg (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom e
    have key : ∀ z, (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom z) = z :=
      fun z => by simp
    rw [key, key] at e'
    rw [ea, eb, hj e']
  have e4 : c₀ = unitOn c := by
    apply Units.ext
    apply ginj
    exact (congrArg Units.val e3).trans (nat (c : T)).symm
  rw [← e4]
  exact hc₀

end GlobalTheory.MumPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparisonRelationsRespectCupStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comparison_relations_respect_cup : ∀ (D : Data) (Λ : Lift D) a b h h', Λ.Rel1 a h → Λ.Rel1 b h' → Λ.Rel2 (cup _ a b) (cupHH D.s h h') := by
  first | exact @GlobalTheory.PDForm.Lift.lift_rel2_cup | exact GlobalTheory.PDForm.Lift.lift_rel2_cup | (intros; apply GlobalTheory.PDForm.Lift.lift_rel2_cup <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexMultiplicationDeRhamForm
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.AdmTransport

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations (inK IsScaledRestr)

variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K]

theorem conj_apply {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    (e : M₁ ≃ₗ[R] M₂) (f : Module.End R M₁) (x : M₂) : e.conjRingEquiv f x = e (f (e.symm x)) := rfl

theorem conj_symm_conj {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    (e : M₁ ≃ₗ[R] M₂) (f : Module.End R M₁) : e.symm.conjRingEquiv (e.conjRingEquiv f) = f := by
  ext x; simp [conj_apply]

theorem inK_injective [IsFractionRing R K] (n : ℕ) : Function.Injective (inK (O := R) K (Fin n → R)) := by
  intro x y hxy
  have h := congrArg (TensorProduct.piScalarRight R K K (Fin n)) hxy
  funext i
  have hi := congrFun h i
  simp [inK] at hi
  apply IsFractionRing.injective R K
  simpa [Algebra.smul_def] using hi

variable {H : Type} [AddCommGroup H] [Module R H]

theorem baseChange_inK (T : Module.End R H) (h : H) : T.baseChange K (inK K H h) = inK K H (T h) := by
  simp [inK, LinearMap.baseChange_tmul]

theorem commute_of_scaledRestr (hinj : Function.Injective (inK (O := R) K H)) {D : R} {N : Module.End K (K ⊗[R] H)}
    {M : Module.End R H} (hM : IsScaledRestr D N M) {T : Module.End R H} (hT : Commute N (T.baseChange K)) :
    Commute M T := by
  refine LinearMap.ext fun h ↦ hinj ?_
  have e := LinearMap.congr_fun hT.eq (inK K H h)
  simp only [Module.End.mul_apply] at e ⊢
  rw [hM, ← baseChange_inK, e, ← LinearMap.map_smul, ← hM, baseChange_inK]

theorem mul_eq_zero_of_scaledRestr (hinj : Function.Injective (inK (O := R) K H)) {D : R}
    {N N' : Module.End K (K ⊗[R] H)} {M M' : Module.End R H} (hM : IsScaledRestr D N M) (hM' : IsScaledRestr D N' M')
    (h0 : N * N' = 0) : M * M' = 0 := by
  refine LinearMap.ext fun h ↦ hinj ?_
  have e := LinearMap.congr_fun h0 (inK K H h)
  simp only [Module.End.mul_apply, LinearMap.zero_apply] at e ⊢
  rw [hM, hM', LinearMap.map_smul, e, smul_zero, smul_zero, map_zero]

theorem bilin_inK (B : LinearMap.BilinForm R H) (u v : H) :
    B.baseChange K (inK K H u) (inK K H v) = algebraMap R K (B u v) := by
  simp [inK, Algebra.algebraMap_eq_smul_one]

theorem skew_of_scaledRestr [IsFractionRing R K] {D : R} {N : Module.End K (K ⊗[R] H)} {M : Module.End R H}
    (hM : IsScaledRestr D N M) (B : LinearMap.BilinForm R H)
    (hs : ∀ x y, B.baseChange K (N x) y + B.baseChange K x (N y) = 0) (u v : H) : B (M u) v + B u (M v) = 0 := by
  apply IsFractionRing.injective R K
  rw [map_add, map_zero, ← bilin_inK, ← bilin_inK, hM, hM, LinearMap.map_smul₂, LinearMap.map_smul, ← smul_add, hs, smul_zero]

theorem orth_of_scaledRestr [IsFractionRing R K] {D : R} {N N' : Module.End K (K ⊗[R] H)} {M M' : Module.End R H}
    (hM : IsScaledRestr D N M) (hM' : IsScaledRestr D N' M') (B : LinearMap.BilinForm R H)
    (hs : ∀ x y, B.baseChange K (N x) (N' y) = 0) (u v : H) : B (M u) (M' v) = 0 := by
  apply IsFractionRing.injective R K
  rw [map_zero, ← bilin_inK, hM, hM', LinearMap.map_smul₂, LinearMap.map_smul, hs, smul_zero, smul_zero]

end GlobalTheory.AdmTransport

namespace GlobalTheory.AdmTransport

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations (inK IsScaledRestr ofF)

theorem admissible_transport_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (𝔠 : FracId (FR E))
    (R : Type) [CommRing R] [IsDomain R] [CharZero R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
    (X₀ : Obj (FR E) 𝔠 (Sp R)) (cm : OAct (orderC c) X₀.A),
    (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF c a) = X₀.rm.act a) →
    ∀ (n : ℕ) (eH : HdR X₀.A ≃ₗ[R] (Fin n → R)) (ψ₀ : LinearMap.BilinForm R (HdR X₀.A)),
    (∀ (c : 𝔠.elt) (ψ : LinearMap.BilinForm R (HdR X₀.A)), IsPolForm (dp0 R) (𝟙 _) X₀.A (X₀.diag c) ψ →
      ∃ (n : ℕ) (t : 𝓞 (FR E)), n ≠ 0 ∧ ∀ x y, (n : R) * ψ x y = ψ₀ x (act (dp0 R) (𝟙 _) X₀.rm t y)) →
    ∀ (I : Type) [Fintype I] (D : R) (N : I → Module.End K (K ⊗[R] (Fin n → R))) (M : I → Module.End R (Fin n → R)),
    (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsScaledRestr D (N i) (M i)) →
    (∀ i (a : OF E), Commute (N i) (((eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF c a)).baseChange K)) →
    (∀ i j, N i * N j = 0) →
    (∀ i x y, LinearMap.BilinForm.baseChange K (ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap : LinearMap.BilinForm R (Fin n → R)) (N i x) y + LinearMap.BilinForm.baseChange K (ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap : LinearMap.BilinForm R (Fin n → R)) x (N i y) = 0) →
    (∀ i j x y, LinearMap.BilinForm.baseChange K (ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap : LinearMap.BilinForm R (Fin n → R)) (N i x) (N j y) = 0) → admitted X₀ (fun i ↦ eH.symm.conjRingEquiv (M i)) := by
  intro E _ _ _ c 𝔠 R _ _ _ K _ _ _ X₀ cm hcm n eH ψ₀ hpol I _ D N M hM hN hNN hskew horth
  have hinj := inK_injective (R := R) (K := K) n

  have hact : ∀ a : OF E, act (dp0 R) (𝟙 _) cm (ofF c a) = act (dp0 R) (𝟙 _) X₀.rm a := by
    intro a
    haveI := cm.hom (ofF c a)
    haveI := X₀.rm.hom a
    rw [act_apply, act_apply]
    exact push_congr _ _ (hcm a)

  have hcomm : ∀ i (a : OF E), Commute (eH.symm.conjRingEquiv (M i)) (act (dp0 R) (𝟙 _) X₀.rm a) := by
    intro i a
    have h1 := commute_of_scaledRestr hinj (hM i) (hN i a)
    have h2 := h1.map eH.symm.conjRingEquiv
    rw [← hact]
    simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, conj_symm_conj] using h2
  set B : LinearMap.BilinForm R (Fin n → R) := ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap with hB
  have hBψ : ∀ x y, ψ₀ x y = B (eH x) (eH y) := by intro x y; simp [hB]
  have hs₀ : ∀ i x y, ψ₀ (eH.symm.conjRingEquiv (M i) x) y + ψ₀ x (eH.symm.conjRingEquiv (M i) y) = 0 := by
    intro i x y
    rw [hBψ, hBψ x]
    simpa [conj_apply] using skew_of_scaledRestr (hM i) B (hskew i) (eH x) (eH y)
  have ho₀ : ∀ i j x y, ψ₀ (eH.symm.conjRingEquiv (M i) x) (eH.symm.conjRingEquiv (M j) y) = 0 := by
    intro i j x y
    rw [hBψ]
    simpa [conj_apply] using orth_of_scaledRestr (hM i) (hM j) B (horth i j) (eH x) (eH y)
  refine ⟨hcomm, fun i j ↦ ?_, fun c' ψ hψ ↦ ?_⟩
  · rw [← map_mul, mul_eq_zero_of_scaledRestr hinj (hM i) (hM j) (hNN i j), map_zero]
  · obtain ⟨m, t, hm, ht⟩ := hpol c' ψ hψ
    have hm' : (m : R) ≠ 0 := Nat.cast_ne_zero.2 hm
    have hT : ∀ i y, act (dp0 R) (𝟙 _) X₀.rm t (eH.symm.conjRingEquiv (M i) y) =
        eH.symm.conjRingEquiv (M i) (act (dp0 R) (𝟙 _) X₀.rm t y) := by
      intro i y
      have := LinearMap.congr_fun (hcomm i t).eq y
      simp only [Module.End.mul_apply] at this
      exact this.symm
    refine ⟨fun i x y ↦ ?_, fun i j x y ↦ ?_⟩
    · apply mul_left_cancel₀ hm'
      rw [mul_add, ht, ht, hT, mul_zero]
      exact hs₀ i x _
    · apply mul_left_cancel₀ hm'
      rw [ht, hT, mul_zero]
      exact ho₀ i j x _

end GlobalTheory.AdmTransport
end
end

