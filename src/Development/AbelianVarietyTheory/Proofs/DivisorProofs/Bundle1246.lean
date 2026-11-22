import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1207
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0116
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0229
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubschemeSubset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0317
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0325
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1171
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1208
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalHeckeScalarOnSphericalVectors
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPosOfPullbackGenericallyEtaleStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiPos_of_pullback_generically_etale : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (V : Y.Opens), (V : Set Y).Nonempty → Etale (V.ι ≫ π) → ∀ L : HermLB p, (L.pull π hπ).SemiPos D → L.SemiPos D := by
  first | exact @GlobalTheory.SemiPosEtale.semiPos_of_pull_etale | exact GlobalTheory.SemiPosEtale.semiPos_of_pull_etale | (intros; apply GlobalTheory.SemiPosEtale.semiPos_of_pull_etale <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparableElementBasisIntegral
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.TwLat.GramUnit

theorem isReduced_of_adjoin {F A : Type} [Field F] [CommRing A] [Algebra F A] [Module.Finite F A]
    (u : A) (P : F[X]) (hP : P.Separable) (hu : aeval u P = 0) (hadj : Algebra.adjoin F {u} = ⊤) :
    IsReduced A := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨N, hN⟩ := hx
  have hxmem : x ∈ Algebra.adjoin F {u} := hadj ▸ Algebra.mem_top
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hxmem
  obtain ⟨f, rfl⟩ := hxmem
  have hdvdP : minpoly F u ∣ P := minpoly.dvd F u hu
  have hsq : Squarefree (minpoly F u) := (hP.of_dvd hdvdP).squarefree
  have hfN : minpoly F u ∣ f ^ N := minpoly.dvd F u (by rw [map_pow]; exact hN)
  obtain ⟨g, hg⟩ := hsq.isRadical N f hfN
  subst hg
  change aeval u (minpoly F u * g) = 0
  rw [map_mul, minpoly.aeval, zero_mul]

theorem eq_zero_of_trace_mul {F A : Type} [Field F] [CharZero F] [CommRing A] [Algebra F A] [Module.Finite F A]
    [IsReduced A] (x : A) (h : ∀ z, Algebra.trace F A (x * z) = 0) : x = 0 := by
  first
  | (rename_i h_2 h_3 h_4 h_5 h_6 h_7; revert F A h_2 h_3 h_4 h_5 h_6 h_7 x h; exact @_root_.GlobalTheory.TraceMulVanishing.trace_mul_eq_zero_imp)
  | exact @_root_.GlobalTheory.TraceMulVanishing.trace_mul_eq_zero_imp
  | exact _root_.GlobalTheory.TraceMulVanishing.trace_mul_eq_zero_imp
  | (apply _root_.GlobalTheory.TraceMulVanishing.trace_mul_eq_zero_imp <;> assumption)
  | (intros; apply _root_.GlobalTheory.TraceMulVanishing.trace_mul_eq_zero_imp <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TraceMulVanishing.trace_mul_eq_zero_imp <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TraceMulVanishing.trace_mul_eq_zero_imp ..)

theorem det_gram_ne_zero {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K) [IsReduced B.A] {m : ℕ}
    (b : Module.Basis (Fin m) K.E B.A) (β : B.A) (hβ : IsUnit β) :
    (Matrix.of fun i j => B.herm β (b i) (b j)).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  set y := ∑ i, v i • b i with hy
  have hlin : ∀ z, B.herm β y z = ∑ i, v i * B.herm β (b i) z := by
    intro z
    simp only [GlobalTheory.UnitLemma.InvAlg.herm, hy, Finset.mul_sum, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, map_smul, smul_eq_mul]
  have hj : ∀ j, B.herm β y (b j) = 0 := by
    intro j
    rw [hlin]
    have := congrFun hv j
    simpa [Matrix.vecMul, dotProduct] using this
  have hsemi : ∀ (d : K.E) (a : B.A), B.σ (d • a) = K.c d • B.σ a := by
    intro d a
    rw [Algebra.smul_def, map_mul, B.σ_alg, ← Algebra.smul_def]
  have hall : ∀ z, Algebra.trace K.E B.A (β * y * z) = 0 := by
    intro z
    have hz : z = ∑ j, K.c (b.repr (B.σ z) j) • B.σ (b j) := by
      conv_lhs => rw [← B.σ_σ z, ← b.sum_repr (B.σ z)]
      rw [map_sum]
      simp only [hsemi]
    rw [hz, Finset.mul_sum, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [mul_smul_comm, map_smul, smul_eq_mul]
    have := hj j
    simp only [GlobalTheory.UnitLemma.InvAlg.herm] at this
    rw [this, mul_zero]
  have hβy : β * y = 0 := eq_zero_of_trace_mul (β * y) hall
  have hy0 : y = 0 := by
    obtain ⟨u, rfl⟩ := hβ
    have := congrArg (fun t => ((u⁻¹ : B.Aˣ) : B.A) * t) hβy
    simpa [← mul_assoc] using this
  exact hv0 (funext (Fintype.linearIndependent_iff.mp b.linearIndependent v hy0))

end GlobalTheory.TwLat.GramUnit

open GlobalTheory.TwLat.GramUnit in

theorem GlobalTheory.TwLat.isUnit_gram_of_separable : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ (u : B.A) (P : K.E[X]), P.Separable → aeval u P = 0 → Algebra.adjoin K.E {u} = ⊤ → ∀ β : B.A, IsUnit β → IsUnit (GlobalTheory.TwLat.gram e b β) := by
  intro E _ _ _ _ w _ K e _ _ _ B m b u P hP hu hadj β hβ
  haveI : IsReduced B.A := isReduced_of_adjoin u P hP hu hadj
  have hd := det_gram_ne_zero B b β hβ
  have hmap : GlobalTheory.TwLat.gram e b β = (Matrix.of fun i j => B.herm β (b i) (b j)).map e := by
    ext i j; rfl
  rw [hmap, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  have := RingHom.map_det (e : K.E →+* w.adicCompletion E) (Matrix.of fun i j => B.herm β (b i) (b j))
  rw [show ((Matrix.of fun i j => B.herm β (b i) (b j)).map e) =
    (e : K.E →+* w.adicCompletion E).mapMatrix (Matrix.of fun i j => B.herm β (b i) (b j)) from rfl, ← this]
  exact (map_ne_zero_iff _ e.injective).mpr hd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafCohomologyDimTwistBoundOfShortExactStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sheafCohomologyDim_twist_bound_of_shortExact : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ (L : LB X), L.IsLB → ∀ S : ShortComplex X.Modules, S.ShortExact → IsFiniteQC S.X₁ → IsFiniteQC S.X₃ → ∀ (i : ℕ) (e : ℕ → ℕ), (∃ C : ℕ, ∀ m : ℕ, hdim k (twist S.X₁ (lbPow L m)) i ≤ C * e m) → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist S.X₃ (lbPow L m)) i ≤ C * e m) → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist S.X₂ (lbPow L m)) i ≤ C * e m) := by
  first | exact @GlobalTheory.hdim_twist_bound_of_shortExact | exact GlobalTheory.hdim_twist_bound_of_shortExact | (intros; apply GlobalTheory.hdim_twist_bound_of_shortExact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafCohomologyDimTwistCutInequalitiesStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sheafCohomologyDim_twist_cut_inequalities : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ (F : X.Modules) [IsFiniteQC F], ∀ (B M M' : LB X) (hB : B.IsLB) (hM : M.IsLB) (hM' : M'.IsLB) (s : B.Sec), Mono (cutHom F hB s) → cls M hM = cls M' hM' + cls B hB → (∀ i, hdim k (twist F M) i ≤ hdim k (twist F M') i + hdim k (twist (cut F hB s) M) i) ∧ (∀ i, hdim k (twist F M') (i + 1) ≤ hdim k (twist (cut F hB s) M) i + hdim k (twist F M) (i + 1)) ∧ hdim k (twist F M') 0 ≤ hdim k (twist F M) 0 := by
  first | exact @GlobalTheory.hdim_twist_cut_inequalities | exact GlobalTheory.hdim_twist_cut_inequalities | (intros; apply GlobalTheory.hdim_twist_cut_inequalities <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafCohomologyDimTwistPushforwardClosedImmersioStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sheafCohomologyDim_twist_pushforward_closedImmersion : ∀ (k : Type) [Field k] (X Z : Scheme.{0}) [Algebra k Γ(X, ⊤)] (g : Z ⟶ X) [IsClosedImmersion g] (L : LB X), L.IsLB → ∀ (G : Z.Modules) (m i : ℕ), letI := algebraΓAlong k g; hdim k (twist ((Scheme.Modules.pushforward g).obj G) (lbPow L m)) i = hdim k (twist G (lbPow (L.pull g) m)) i := by
  first | exact @GlobalTheory.hdim_twist_pushforward_lbPow_of_isClosedImmersion | exact GlobalTheory.hdim_twist_pushforward_lbPow_of_isClosedImmersion | (intros; apply GlobalTheory.hdim_twist_pushforward_lbPow_of_isClosedImmersion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShearedGenericFlagEqGenericFlagAtSpecial
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush.Meet

theorem val_spMap_pt {F : Type} [Field F] (Y : Var F) {K : Type} [Field K] (σ : Y.Fn →+* K) (x : Y.Fn) :
    (ratOf Y).val (spMap σ ≫ (ratOf Y).pt) x = σ x := by
  have hx : x ∈ (ratOf Y).O ((ratOf Y).pt (IsLocalRing.closedPoint Y.Fn)) := by
    refine (congrArg (fun z => x ∈ (ratOf Y).O z) ((ratOf Y).pt_apply _)).mpr ?_
    rw [RatModel.O_genericPoint]; exact Algebra.mem_top
  have h := RatModel.val_spMap_comp (M := ratOf Y) σ (ratOf Y).pt specializes_rfl ⟨x, hx⟩
  rw [RatModel.valLoc_eq_val] at h
  exact h.trans (congrArg σ (RatModel.val_pt x))

open GlobalTheory.FlagBundle.ClosedPt in

theorem meet : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ B ∈ E'.S (genericPoint Y.X), ∀ A ∈ E.S (f (genericPoint Y.X)), ∀ (τ : ι) (a b : Fin (m τ)), a < b → ∀ (K : Type) [Field K] (V : ValuationSubring K) (c : Y.Fn →+* V) (t : V), IsLocalRing.residue V t = 0 → ∀ v₂ : Sp V ⟶ Y.X, v₂ ≫ f = spMap c ≫ (ratOf Y).pt ≫ f → Bears E' φ A (shear τ a b (t : K) * (B * (A.map φ)⁻¹).map ((algebraMap V K).comp c)) (spMap (algebraMap V K) ≫ v₂) → spMap (IsLocalRing.residue V) ≫ spMap c ≫ (ratOf Y).pt = spMap (IsLocalRing.residue V) ≫ v₂ := by
  intro F _ X Y ι _ m E E' φ f hf B hB A hA τ a b hab K _ V c t ht v₂ e hbear
  have hM := hf.sub _ B hB A hA
  obtain ⟨-, -, -, hsm⟩ := GlobalTheory.T.blockMatrixElementaryShear_properties ι m τ a b hab V t
  obtain ⟨-, -, hs0, -⟩ := GlobalTheory.T.blockMatrixElementaryShear_properties ι m τ a b hab (IsLocalRing.ResidueField V) 0
  have hpt : ∀ (R : Type) [CommRing R] (g : Y.Fn →+* R) (w : Sp R),
      (spMap g ≫ (ratOf Y).pt) w = genericPoint Y.X := fun R _ g w =>
    (Scheme.Hom.comp_apply _ _ _).trans ((ratOf Y).pt_apply _)
  have hf₂ : f (v₂ (IsLocalRing.closedPoint V)) = f (genericPoint Y.X) := by
    refine (Scheme.Hom.comp_apply _ _ _).symm.trans ?_
    rw [e]
    exact (Scheme.Hom.comp_apply (spMap c ≫ (ratOf Y).pt) f _).trans (congrArg f (hpt _ c _))
  obtain ⟨A₂, hA₂⟩ := E'.nonempty (v₂ (IsLocalRing.closedPoint V))
  have hM₂ := hf.sub _ A₂ hA₂ A ((congrArg (fun z => A ∈ E.S z) hf₂).mpr hA)
  obtain ⟨A₂', hA₂', hpar⟩ := hbear
  have hA₂g : A₂ ∈ E'.S ((spMap (algebraMap V K) ≫ v₂) (IsLocalRing.closedPoint K)) :=
    Fr.mem_of_specializes hA₂ (gen_specializes v₂ _)
  have hsp₂ := gen_specializes (L := K) v₂ (IsLocalRing.closedPoint K)
  have hG := (Fr.mem_iff hA₂g).1 hA₂'
  have hM₂g : Par 0 ((ratOf Y).O ((spMap (algebraMap V K) ≫ v₂) (IsLocalRing.closedPoint K))).toSubring
      (A₂ * (A.map φ)⁻¹) :=
    hM₂.mono le_rfl fun _ hx => RatModel.O_le_of_specializes hsp₂ hx
  set ψ := RatModel.valHom (M := ratOf Y) (spMap (algebraMap V K) ≫ v₂) _
    (RatModel.range_eq_singleton _ (IsLocalRing.closedPoint K))
  have hv : ∀ x : ((ratOf Y).O ((spMap (algebraMap V K) ≫ v₂) (IsLocalRing.closedPoint K))).toSubring,
      (ratOf Y).val (spMap (algebraMap V K) ≫ v₂) x = ψ x := fun _ => rfl
  have heqM : A₂' * (A.map φ)⁻¹ = (A₂' * A₂⁻¹) * (A₂ * (A.map φ)⁻¹) := by
    rw [mul_assoc, ← mul_assoc A₂⁻¹, Mat.inv_mul (Fr.det_ne hA₂), one_mul]
  have hmap : (A₂' * (A.map φ)⁻¹).map ((ratOf Y).val (spMap (algebraMap V K) ≫ v₂)) =
      (A₂' * A₂⁻¹).map ((ratOf Y).val (spMap (algebraMap V K) ≫ v₂)) *
        (A₂ * (A.map φ)⁻¹).map ((ratOf Y).val (spMap (algebraMap V K) ≫ v₂)) := by
    rw [heqM]
    exact Par.map_mul_of hG hM₂g ((ratOf Y).val (spMap (algebraMap V K) ≫ v₂)) ψ hv
  have hGv := Par.map_of hG ((ratOf Y).val (spMap (algebraMap V K) ≫ v₂)) ψ hv
  have hpar2 := hpar
  erw [hmap] at hpar2
  rw [Mat.mul_inv_rev] at hpar2
  clear hpar
  have hL := hpar2.mul hGv
  rw [mul_assoc, mul_assoc, mul_assoc, Mat.inv_mul hGv.det_ne, mul_one, ← mul_assoc] at hL
  rw [map_val (algebraMap V K) v₂ _ (fun τ a b => (hM₂ τ).1 a b)] at hL
  have hN : ∀ (S : Type) [CommRing S] (g : V →+* S),
      (shear τ a b t * (B * (A.map φ)⁻¹).map c).map g =
        shear τ a b (g t) * (B * (A.map φ)⁻¹).map (g.comp c) := fun S _ g => by
    rw [← hsm S g]
    funext σ
    exact Matrix.map_mul
  have hN1 := hN K (algebraMap V K)
  have hN2 := hN _ (IsLocalRing.residue V)
  rw [ht, hs0, one_mul] at hN2
  have hh : Par 0 ⊤ ((B * (A.map φ)⁻¹).map ((IsLocalRing.residue V).comp c)) :=
    hM.map _ fun _ _ => trivial
  have hk₂ := par_val (IsLocalRing.residue V) v₂ hM₂
  have hD := descend (L := K) (shear τ a b t * (B * (A.map φ)⁻¹).map c)
    (vals v₂ _ (fun τ a b => (hM₂ τ).1 a b)) (by rw [hN2]; exact hh.det_ne)
    (by rw [← map_val]; exact hk₂.det_ne) (by rw [hN1]; exact hL)
  rw [hN2, ← map_val] at hD
  have ec : spMap (IsLocalRing.residue V) ≫ spMap c ≫ (ratOf Y).pt =
      spMap ((IsLocalRing.residue V).comp c) ≫ (ratOf Y).pt := by
    rw [← Category.assoc, ← Spec.map_comp]
    rfl
  have hb₂ : Bears E' φ A ((B * (A.map φ)⁻¹).map ((IsLocalRing.residue V).comp c))
      (spMap (IsLocalRing.residue V) ≫ v₂) :=
    ⟨A₂, (congrArg (fun z => A₂ ∈ E'.S z) (closedPt_comp v₂)).mpr hA₂, hD⟩
  have hb₁ : Bears E' φ A ((B * (A.map φ)⁻¹).map ((IsLocalRing.residue V).comp c))
      (spMap ((IsLocalRing.residue V).comp c) ≫ (ratOf Y).pt) := by
    refine ⟨B, (congrArg (fun z => B ∈ E'.S z) (hpt _ _ _)).mpr hB, ?_⟩
    rw [show (ratOf Y).val (spMap ((IsLocalRing.residue V).comp c) ≫ (ratOf Y).pt) =
      ⇑((IsLocalRing.residue V).comp c) from funext (val_spMap_pt Y _), Mat.mul_inv hh.det_ne]
    exact Par.one
  have hAk : A ∈ E.S (((spMap (IsLocalRing.residue V) ≫ v₂) ≫ f)
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField V))) := by
    refine (congrArg (fun z => A ∈ E.S z) ?_).mpr hA
    exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg f (closedPt_comp v₂)).trans hf₂)
  obtain ⟨p, -, hp⟩ := hf.lifts _ _ A hAk _ hh
  refine (ec.trans (hp _ ⟨?_, hb₁⟩)).trans (hp _ ⟨rfl, hb₂⟩).symm
  rw [← ec]
  exact congrArg (spMap (IsLocalRing.residue V) ≫ ·) e.symm

end GlobalTheory.FlagPush.Meet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShiftSecondBundleNormPairNormBallGenerationStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shiftSecondBundleNormPair_norm_ball_generation : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (P : Pair p) (u : ℝ), (∀ (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField), (shiftA P u).nu a b σ y f = P.nu a b σ y f * Real.exp (-(b * u))) ∧ (∀ (a b : ℤ) (R : ℝ), (shiftA P u).Bl a b R = P.Bl a b (R * Real.exp (b * u))) ∧ (∀ c : ℕ, GenAt P c → GenAt (shiftA P u) c) := by
  first | exact @GlobalTheory.HSNef.shiftA_props | exact GlobalTheory.HSNef.shiftA_props | (intros; apply GlobalTheory.HSNef.shiftA_props <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelMeanValueNonnegative
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.OrbFinAf.KottLat

variable {p : ℕ} [Fact p.Prime]

theorem isIntV_add (G : HTGroup p) (v : AwayP p) {a b : Qv v ⊗[ℚ] G.C} (ha : IsIntV G v a)
    (hb : IsIntV G v b) : IsIntV G v (a + b) := fun i => by
  rw [map_add, Finsupp.add_apply]; exact Subring.add_mem _ (ha i) (hb i)

theorem isIntV_zero (G : HTGroup p) (v : AwayP p) : IsIntV G v 0 := fun i => by
  rw [map_zero, Finsupp.zero_apply]; exact Subring.zero_mem _

theorem eventually_isIntV_map (G : HTGroup p) (y : AfP p ⊗[ℚ] G.C) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)),
      IsIntV G v (Algebra.TensorProduct.map (AfP.eval v) (AlgHom.id ℚ G.C) y) := by
  induction y using TensorProduct.induction_on with
  | zero => exact Filter.Eventually.of_forall fun v => by rw [map_zero]; exact isIntV_zero G v
  | tmul a c =>
    have h1 : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)),
        AfP.eval v a ∈ v.1.adicCompletionIntegers ℚ := a.2
    have h2 : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ i,
        algebraMap ℚ (Qv v) ((Module.finBasis ℚ G.C).repr c i) ∈ v.1.adicCompletionIntegers ℚ := by
      simp only [Filter.eventually_all]; intro i; exact eventually_rat_mem_integers _
    filter_upwards [h1, h2] with v hv1 hv2 i
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsIntV, basV,
      Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
    exact Subring.mul_mem _ hv1 (hv2 i)
  | add y z hy hz =>
    filter_upwards [hy, hz] with v h1 h2
    rw [map_add]; exact isIntV_add G v h1 h2

end GlobalTheory.OrbFinAf.KottLat

namespace GlobalTheory.OrbFinAf.KottLat

theorem conj_integral {A K : Type} [Ring A] [CommRing K] {n : ℕ} (R : Subring K)
    (Φ : Matrix (Fin n) (Fin n) K ≃+* A) (hfin : Set.Finite {I : Ideal R | I.IsMaximal})
    (Q : Polynomial R) (hQs : Q.Separable) (γ₀ : Aˣ) (hQm : Q.map R.subtype = (Φ.symm γ₀).charpoly)
    (hγ : ∀ i j, Φ.symm γ₀ i j ∈ R) (g : Aˣ) (hδ : ∀ i j, Φ.symm ((g⁻¹ * γ₀ * g : Aˣ) : A) i j ∈ R) :
    ∃ U : Aˣ, U * (g⁻¹ * γ₀ * g) = γ₀ * U ∧ (∀ i j, Φ.symm (U : A) i j ∈ R) ∧
      (∀ i j, Φ.symm ((U⁻¹ : Aˣ) : A) i j ∈ R) := by
  have lift : ∀ a : A, (∀ i j, Φ.symm a i j ∈ R) →
      ∃ M : Matrix (Fin n) (Fin n) R, M.map R.subtype = Φ.symm a :=
    fun a h => ⟨fun i j => ⟨_, h i j⟩, by ext i j; rfl⟩
  obtain ⟨Γ, hΓ⟩ := lift _ hγ
  obtain ⟨Δ, hΔ⟩ := lift _ hδ
  have hcΓ : Γ.charpoly.map R.subtype = (Φ.symm γ₀).charpoly := by
    rw [← Matrix.charpoly_map, hΓ]
  have hcΔ : Δ.charpoly.map R.subtype = (Φ.symm γ₀).charpoly := by
    rw [← Matrix.charpoly_map, hΔ]
    have e : Φ.symm ((g⁻¹ * γ₀ * g : Aˣ) : A) =
        (((Units.map (Φ.symm : A ≃+* _).toRingHom.toMonoidHom g)⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) :
          Matrix (Fin n) (Fin n) K) * Φ.symm γ₀ *
        ((Units.map (Φ.symm : A ≃+* _).toRingHom.toMonoidHom g : (Matrix (Fin n) (Fin n) K)ˣ) :
          Matrix (Fin n) (Fin n) K) := by
      rw [Units.val_mul, Units.val_mul, map_mul, map_mul]; rfl
    rw [e, Matrix.charpoly_mul_comm, ← mul_assoc, Units.mul_inv, one_mul]
  have hinj : Function.Injective (Polynomial.map R.subtype) :=
    Polynomial.map_injective _ Subtype.val_injective
  have heq : Γ.charpoly = Δ.charpoly := hinj (hcΓ.trans hcΔ.symm)
  have hQ : Q = Γ.charpoly := hinj (hQm.trans hcΓ.symm)
  obtain ⟨u, hu⟩ := GlobalTheory.T.semilocal_conjugate_same_charpoly R hfin n Γ Δ heq (hQ ▸ hQs)
  let F : Matrix (Fin n) (Fin n) R →* A := (Φ.toRingHom.comp R.subtype.mapMatrix).toMonoidHom
  let U : Aˣ := Units.map F u
  have hUs : Φ.symm (U : A) = (u : Matrix (Fin n) (Fin n) R).map R.subtype := Φ.symm_apply_apply _
  have hUs' : Φ.symm ((U⁻¹ : Aˣ) : A) = ((u⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).map R.subtype := by
    rw [show U⁻¹ = Units.map F u⁻¹ from (map_inv (Units.map F) u).symm]
    exact Φ.symm_apply_apply _
  refine ⟨U, Units.ext (Φ.symm.injective ?_), fun i j => ?_, fun i j => ?_⟩
  · rw [Units.val_mul U, Units.val_mul γ₀, map_mul, map_mul, hUs, ← hΔ, ← hΓ, ← Matrix.map_mul,
      ← Matrix.map_mul, hu]
  · rw [hUs, Matrix.map_apply]; exact (u : Matrix (Fin n) (Fin n) R) i j |>.2
  · rw [hUs', Matrix.map_apply]; exact ((u⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j |>.2

end GlobalTheory.OrbFinAf.KottLat

namespace GlobalTheory.OrbFinAf.KottLat

end GlobalTheory.OrbFinAf.KottLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SigBasisApply
section
namespace GlobalTheory.ScalarSigmaBasis

open GlobalTheory.UnitLemma

variable {K : UQ} (B : InvAlg K)

theorem sig_smul (r : K.E) (x : B.A) : B.σ (r • x) = K.c r • B.σ x := by
  rw [Algebra.smul_def, map_mul, B.σ_alg, ← Algebra.smul_def]

theorem sig_sum {ι : Type} (s : Finset ι) (f : ι → K.E) (v : ι → B.A) :
    B.σ (∑ i ∈ s, f i • v i) = ∑ i ∈ s, K.c (f i) • B.σ (v i) := by
  rw [map_sum]; simp only [sig_smul]

noncomputable def sigBasis {n : ℕ} (b : Module.Basis (Fin n) K.E B.A) : Module.Basis (Fin n) K.E B.A :=
  Module.Basis.mk (v := fun i => B.σ (b i))
    (by
      rw [Fintype.linearIndependent_iff]
      intro f hf i
      have h1 : B.σ (∑ k, f k • B.σ (b k)) = 0 := by rw [hf, map_zero]
      rw [sig_sum] at h1
      simp only [B.σ_σ] at h1
      have h2 := (Fintype.linearIndependent_iff.mp b.linearIndependent) _ h1 i
      have : K.c (f i) = K.c 0 := by rw [h2, map_zero]
      exact K.c.injective this)
    (by
      intro x _
      have h := sig_sum B Finset.univ (fun k => b.repr (B.σ x) k) (fun k => b k)
      have hx : x = ∑ k, K.c (b.repr (B.σ x) k) • B.σ (b k) := by
        rw [← h, b.sum_repr, B.σ_σ]
      rw [hx]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))

theorem sigBasis_apply {n : ℕ} (b : Module.Basis (Fin n) K.E B.A) (i : Fin n) :
    sigBasis B b i = B.σ (b i) := by
  simp [sigBasis]

theorem sigBasis_repr {n : ℕ} (b : Module.Basis (Fin n) K.E B.A) (z : B.A) (k : Fin n) :
    (sigBasis B b).repr (B.σ z) k = K.c (b.repr z k) := by
  have hz : B.σ z = ∑ i, K.c (b.repr z i) • sigBasis B b i := by
    conv_lhs => rw [← b.sum_repr z]
    rw [sig_sum]
    simp only [sigBasis_apply]
  rw [hz, Module.Basis.repr_sum_self]

theorem trace_sig (y : B.A) : Algebra.trace K.E B.A (B.σ y) = K.c (Algebra.trace K.E B.A y) := by
  let b := Module.finBasis K.E B.A
  rw [Algebra.trace_eq_matrix_trace (sigBasis B b), Algebra.trace_eq_matrix_trace b]
  simp only [Matrix.trace, Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sigBasis_apply, ← map_mul, sigBasis_repr]

theorem core (a : ℕ) (β : B.A) (hβ : B.σ β = β * ((-1 : B.A) ^ (a - 1) * B.g))
    (b : Module.Basis (Fin a) K.E B.A) (i j : Fin a) :
    K.c (B.herm β (b i) (b j)) = (-1 : K.E) ^ (a - 1) *
      ∑ k, B.herm β (b k) (b i) * LinearMap.toMatrix b b (LinearMap.mulLeft K.E B.g) k j := by
  have hg : B.g * b j = ∑ k, b.repr (B.g * b j) k • b k := (b.sum_repr _).symm
  have e1 : B.σ (β * b i * B.σ (b j)) =
      algebraMap K.E B.A ((-1 : K.E) ^ (a - 1)) * (β * (B.g * b j) * B.σ (b i)) := by
    rw [map_mul, map_mul, B.σ_σ, hβ]
    simp only [map_pow, map_neg, map_one]
    ring
  have e2 : β * (B.g * b j) * B.σ (b i) = ∑ k, b.repr (B.g * b j) k • (β * b k * B.σ (b i)) := by
    conv_lhs => rw [hg]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_smul_comm, smul_mul_assoc]
  rw [InvAlg.herm, ← trace_sig, e1, e2, ← Algebra.smul_def, LinearMap.map_smul, map_sum, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.map_smul, smul_eq_mul, LinearMap.toMatrix_apply, LinearMap.mulLeft_apply, mul_comm]
  rfl

theorem main : ∀ {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K) (L : Type) [inst : Field L] (e : GlobalTheory.UnitLemma.UQ.E K ≃+* L) (c : L →+* L), (∀ (x : GlobalTheory.UnitLemma.UQ.E K), (e : GlobalTheory.UnitLemma.UQ.E K → L) ((GlobalTheory.UnitLemma.UQ.c K : GlobalTheory.UnitLemma.UQ.E K → GlobalTheory.UnitLemma.UQ.E K) x) = (c : L → L) ((e : GlobalTheory.UnitLemma.UQ.E K → L) x)) → ∀ (a : ℕ) (β : GlobalTheory.UnitLemma.InvAlg.A B), (GlobalTheory.UnitLemma.InvAlg.σ B : GlobalTheory.UnitLemma.InvAlg.A B → GlobalTheory.UnitLemma.InvAlg.A B) β = β * ((-1 : GlobalTheory.UnitLemma.InvAlg.A B) ^ (a - (1 : ℕ)) * GlobalTheory.UnitLemma.InvAlg.g B) → ∀ (b : Module.Basis (Fin a) (GlobalTheory.UnitLemma.UQ.E K) (GlobalTheory.UnitLemma.InvAlg.A B)), Matrix.map (Matrix.map ((Matrix.of : (Fin a → Fin a → GlobalTheory.UnitLemma.UQ.E K) → Matrix (Fin a) (Fin a) (GlobalTheory.UnitLemma.UQ.E K)) fun (i j : Fin a) ↦ GlobalTheory.UnitLemma.InvAlg.herm B β ((b : Fin a → GlobalTheory.UnitLemma.InvAlg.A B) i) ((b : Fin a → GlobalTheory.UnitLemma.InvAlg.A B) j)) (⇑e : GlobalTheory.UnitLemma.UQ.E K → L)) (⇑c : L → L) = (-1 : L) ^ (a - (1 : ℕ)) • (Matrix.transpose (Matrix.map ((Matrix.of : (Fin a → Fin a → GlobalTheory.UnitLemma.UQ.E K) → Matrix (Fin a) (Fin a) (GlobalTheory.UnitLemma.UQ.E K)) fun (i j : Fin a) ↦ GlobalTheory.UnitLemma.InvAlg.herm B β ((b : Fin a → GlobalTheory.UnitLemma.InvAlg.A B) i) ((b : Fin a → GlobalTheory.UnitLemma.InvAlg.A B) j)) (⇑e : GlobalTheory.UnitLemma.UQ.E K → L)) * Matrix.map ((LinearMap.toMatrix b b : (GlobalTheory.UnitLemma.InvAlg.A B →ₗ[GlobalTheory.UnitLemma.UQ.E K] GlobalTheory.UnitLemma.InvAlg.A B) → Matrix (Fin a) (Fin a) (GlobalTheory.UnitLemma.UQ.E K)) (LinearMap.mulLeft (GlobalTheory.UnitLemma.UQ.E K) (GlobalTheory.UnitLemma.InvAlg.g B))) (⇑e : GlobalTheory.UnitLemma.UQ.E K → L)) := by
  intro K B L _ e c hc a β hβ b
  ext i j
  simp only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply,
    smul_eq_mul]
  rw [← hc, core B a β hβ b i j]
  simp only [map_mul, map_sum, map_pow, map_neg, map_one]

end GlobalTheory.ScalarSigmaBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelDimGeomConnectedDescendFieldExtensionStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothOfRelDim_geomConnected_descend_fieldExtension : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → ∀ D : ℕ, Nonempty X → SmoothOfRelativeDimension D q → GeometricallyConnected q → SmoothOfRelativeDimension D p ∧ GeometricallyConnected p := by
  first | exact @GlobalTheory.FieldDescentSm.smoothOfRelativeDimension_and_geometricallyConnected_descend | exact GlobalTheory.FieldDescentSm.smoothOfRelativeDimension_and_geometricallyConnected_descend | (intros; apply GlobalTheory.FieldDescentSm.smoothOfRelativeDimension_and_geometricallyConnected_descend <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializesOfPointLocalRingLeSeparatedStatement
section
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.specializes_of_pointLocalRing_le_separated : ∀ (X : Scheme.{0}) [IsIntegral X] [X.IsSeparated] (x z : X), locRing x ≤ locRing z → z ⤳ x := by
  first | exact @GlobalTheory.specializes_of_locRing_le | exact GlobalTheory.specializes_of_locRing_le | (intros; apply GlobalTheory.specializes_of_locRing_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalHeckeScalarOnSphericalVectorsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphericalHecke_scalar_on_spherical_vectors : ∀ {D : D7} {V : HSp D} {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (Q : principalLevelFrame.RowPsi V n), StdPsi hF Q → ∀ (π : Formalism.L2.NG.FinTyp D.host.E n) Pr d B, SphOp V Pr d B → ∃ a : ℂ, ∀ x ∈ π.S, (∀ κ, Q.ψ κ ∈ hyp V Pr → Formalism.L2.NG.rt D.host.E n κ x = x) → principalLevelFrame.Hecke₃ Q B x = a • x := by
  first | exact @GlobalTheory.SphScalar.spherical_scalar | exact GlobalTheory.SphScalar.spherical_scalar | (intros; apply GlobalTheory.SphScalar.spherical_scalar <;> assumption)
end

