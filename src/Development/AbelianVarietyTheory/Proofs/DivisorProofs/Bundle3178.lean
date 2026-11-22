import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1022
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0054
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3136
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3137
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2357
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3107
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3138
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2045
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3139
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2633

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPosPullbackGenericallyBirational
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SemiPullBir

theorem exists_isIso_restrict {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X)
    [IsSeparated π] [LocallyOfFiniteType π] (hη : π (genericPoint Y) = genericPoint X)
    (hd : π.residueDegree (genericPoint Y) = 1) :
    ∃ U : X.Opens, (U : Set X).Nonempty ∧ IsIso (π ∣_ U) := by
  have hFX : IsField (X.presheaf.stalk (π (genericPoint Y))) := by
    rw [hη]
    exact Field.toIsField X.functionField
  have hFY : IsField (Y.presheaf.stalk (genericPoint Y)) := Field.toIsField Y.functionField
  have hrX : Function.Bijective (X.residue (π (genericPoint Y))).hom := by
    refine ⟨?_, IsLocalRing.residue_surjective⟩
    letI := hFX.toField
    exact RingHom.injective _
  have hrY : Function.Bijective (Y.residue (genericPoint Y)).hom := by
    refine ⟨?_, IsLocalRing.residue_surjective⟩
    letI := hFY.toField
    exact RingHom.injective _
  have hκ : Function.Bijective (π.residueFieldMap (genericPoint Y)).hom := by
    letI := (π.residueFieldMap (genericPoint Y)).hom.toAlgebra
    have h1 : Module.finrank (X.residueField (π (genericPoint Y))) (Y.residueField (genericPoint Y)) = 1 := hd
    refine ⟨RingHom.injective _, fun y => ?_⟩
    have htop := Subalgebra.bot_eq_top_iff_finrank_eq_one.2 h1
    have hy : y ∈ (⊥ : Subalgebra (X.residueField (π (genericPoint Y))) (Y.residueField (genericPoint Y))) := by
      rw [htop]; exact Algebra.mem_top
    obtain ⟨a, ha⟩ := Algebra.mem_bot.1 hy
    exact ⟨a, ha⟩
  have hst : Function.Bijective (π.stalkMap (genericPoint Y)).hom := by
    have e := Scheme.residue_residueFieldMap (f := π) (genericPoint Y)
    have e' : (Y.residue (genericPoint Y)).hom.comp (π.stalkMap (genericPoint Y)).hom =
        (π.residueFieldMap (genericPoint Y)).hom.comp (X.residue (π (genericPoint Y))).hom := by
      rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, ← e]
    have hc : Function.Bijective ((Y.residue (genericPoint Y)).hom.comp (π.stalkMap (genericPoint Y)).hom) := by
      rw [e']; exact hκ.comp hrX
    refine (Function.Bijective.of_comp_iff' hrY _).1 hc
  have : IsIso (π.stalkMap (genericPoint Y)) := (ConcreteCategory.isIso_iff_bijective _).2 hst
  let φ : Spec (X.presheaf.stalk (π (genericPoint Y))) ⟶ Y :=
    Spec.map (inv (π.stalkMap (genericPoint Y))) ≫ Y.fromSpecStalk (genericPoint Y)
  have hφ : φ ≫ π = X.fromSpecStalk (π (genericPoint Y)) ≫ 𝟙 X := by
    simp only [φ, Category.assoc, Category.comp_id]
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc, ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id,
      Category.id_comp]
  obtain ⟨U, hU, g, hg₁, hg₂⟩ := spread_out_of_isGermInjective' (𝟙 X) π φ hφ
  rw [Category.comp_id] at hg₂
  have : IsDominant (Y.fromSpecStalk (genericPoint Y)) :=
    ⟨((dense_iff_closure_eq.2 (genericPoint_spec Y)).mono
      (Set.singleton_subset_iff.2 ⟨_, Scheme.fromSpecStalk_closedPoint⟩))⟩
  have : IsDominant φ := inferInstance
  have : IsDominant g := by
    rw [hg₁] at this
    exact IsDominant.of_comp (U.fromSpecStalkOfMem _ hU) g
  exact ⟨U, ⟨_, hU⟩, GlobalTheory.ZH.isIso_morphismRestrict_of_local_dominant_sections π U fun y hy =>
    ⟨U, U.ι, inferInstance, g, ⟨⟨y, hy⟩, rfl⟩, by simp, ‹_›, hg₂⟩⟩

theorem semiPos_pull : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) = 1 → ∀ L : HermLB p, L.SemiPos D → (L.pull π hπ).SemiPos D := by
  intro k _ X _ p D hp Y _ q hq π hπ hη hd L hL
  have hpr : IsProper q := GlobalTheory.SchemeWords.isProper_of_isProjOver hq.isProjOver
  have hsep : IsSeparated (π ≫ p) := by rw [hπ]; infer_instance
  have hft : LocallyOfFiniteType (π ≫ p) := by rw [hπ]; infer_instance
  have : IsSeparated π := IsSeparated.of_comp π p
  have : LocallyOfFiniteType π := locallyOfFiniteType_of_comp π p
  obtain ⟨U, hU, hi⟩ := exists_isIso_restrict π hη hd
  exact (GlobalTheory.SemiPosBir.semiPos_iff_pull k X Y p q D hp hq π hπ U hU hi L).1 hL

end GlobalTheory.SemiPullBir
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpBundleFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep

variable {V V₁ : Type} [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁]

def sharpPair (ρ : V →+* V₁) (Q : Data V) (D : DegPre V₁) (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B))
    (a b : Fin 8) : D.P.A.left ⟶ (G2 Q.B).left :=
  (lift (pushPt (isGrpPullback_pullback Q.B (spMap ρ)).1.w (pr a))
    (pushPt (isGrpPullback_pullback Q.B (spMap ρ)).1.w (pr b))).left

theorem sharp_cls_pair (W : Matrix (Fin 8) (Fin 8) ℤ) (ρ : V →+* V₁) (Q : Data V) (D : DegPre V₁)
    (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B)) (a b : Fin 8) :
    (∏ I : ULift.{0} (Finset (Fin 2)), GlobalTheory.PrimNorm.cls Q.M.L (sharpPair ρ Q D pr a b ≫ (psum Q.B (x2 Q.B) I.down).left) ^
        ((-1 : ℤ) ^ (2 - I.down.card))) ^ W a b =
      ∏ k : Fin 4, GlobalTheory.PrimNorm.cls Q.M.L (lamPts (pr a) (pr b) k ≫ pullback.fst Q.B.hom (spMap ρ)) ^
        (-(W a b * negε k)) := by
  have h := isGrpPullback_pullback Q.B (spMap ρ)
  set xa := pushPt h.1.w (pr a) with hxa
  set xb := pushPt h.1.w (pr b) with hxb
  have e := GlobalTheory.PrimNorm.prod_square (lift xa xb) (fst Q.B Q.B) (snd Q.B Q.B) (GlobalTheory.PrimNorm.cls Q.M.L)
  rw [lift_fst, lift_snd] at e
  have e' : sharpPair ρ Q D pr a b = (lift xa xb).left := rfl
  rw [e', show x2 Q.B = ![fst Q.B Q.B, snd Q.B Q.B] from rfl, e]
  have m : (pr a * pr b).left ≫ pullback.fst Q.B.hom (spMap ρ) = (xa * xb).left :=
    (h.2 D.P.A (pr a) (pr b) xa xb rfl rfl).symm
  have o : (1 : D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B).left ≫ pullback.fst Q.B.hom (spMap ρ) =
      (1 : Over.mk (D.P.A.hom ≫ spMap ρ) ⟶ Q.B).left :=
    congrArg (fun z => z.left) (map_one (pushHom h D.P.A))
  rw [Fin.prod_univ_four]
  simp only [lamPts, negε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, m, o]
  change GlobalTheory.PrimNorm.diff₂ _ xa xb ^ W a b = _
  simp only [GlobalTheory.PrimNorm.diff₂]
  have ha : (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) = xa.left := rfl
  have hb : (pr b).left ≫ pullback.fst Q.B.hom (spMap ρ) = xb.left := rfl
  rw [ha, hb]
  simp only [mul_neg, neg_neg, zpow_neg, mul_zpow, inv_zpow]
  ac_rfl

theorem sharp_bundle {W₀ : Type} [CommRing W₀] (W : Matrix (Fin 8) (Fin 8) ℤ) (ρ : V →+* V₁) (Q : Data V) (D : DegPre V₁)
    (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B))
    (w : LB.Iso D.P.L (LB.LinComb Q.M.L (K := (Fin 8 × Fin 8) × Fin 4)
      (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ)) (fun k => -(W k.1.1 k.1.2 * negε k.2))))
    (hw : w.IsGen) (B₀ : Over (Sp W₀)) [GrpObj B₀] [IsCommMonObj B₀] (M₀ : LB B₀.left) (hM₀ : M₀.IsLB)
    (β₂ : (G2 Q.B).left ⟶ (G2 B₀).left) (w₀ : LB.Iso (abelian₂ Q.B Q.M.L) ((abelian₂ B₀ M₀).pull β₂)) (hw₀ : w₀.IsGen) :
    LBIso D.P.L (LB.LinComb (abelian₂ B₀ M₀) (K := Fin 8 × Fin 8) (fun p => sharpPair ρ Q D pr p.1 p.2 ≫ β₂)
      (fun p => W p.1 p.2)) := by
  have hL : Q.M.L.IsLB := Q.M.isLB
  have hLam : (abelian₂ Q.B Q.M.L).IsLB := DVR.linComb_isLB _ hL _ _
  have hLam₀ : (abelian₂ B₀ M₀).IsLB := DVR.linComb_isLB _ hM₀ _ _
  have hS : (LB.LinComb Q.M.L (K := (Fin 8 × Fin 8) × Fin 4)
      (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ))
      (fun k => -(W k.1.1 k.1.2 * negε k.2))).IsLB := DVR.linComb_isLB _ hL _ _
  have h₂ : LBIso (LB.LinComb (abelian₂ Q.B Q.M.L) (K := Fin 8 × Fin 8) (fun p => sharpPair ρ Q D pr p.1 p.2)
      (fun p => W p.1 p.2)) (LB.LinComb Q.M.L (K := (Fin 8 × Fin 8) × Fin 4)
      (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ))
      (fun k => -(W k.1.1 k.1.2 * negε k.2))) := by
    refine GlobalTheory.PrimNorm.lbIso_nested hL _ _ _ _ _ _ ?_
    refine Eq.trans ?_ (Fintype.prod_prod_type _).symm
    exact Finset.prod_congr rfl fun p _ => sharp_cls_pair W ρ Q D pr p.1 p.2
  have h₃ : LBIso (LB.LinComb (abelian₂ Q.B Q.M.L) (K := Fin 8 × Fin 8) (fun p => sharpPair ρ Q D pr p.1 p.2)
      (fun p => W p.1 p.2)) (LB.LinComb ((abelian₂ B₀ M₀).pull β₂) (K := Fin 8 × Fin 8)
      (fun p => sharpPair ρ Q D pr p.1 p.2) (fun p => W p.1 p.2)) :=
    GlobalTheory.PowPrimitive.lbIso_linComb ⟨w₀, hw₀⟩ _ _
  have h₄ : LBIso (LB.LinComb ((abelian₂ B₀ M₀).pull β₂) (K := Fin 8 × Fin 8)
      (fun p => sharpPair ρ Q D pr p.1 p.2) (fun p => W p.1 p.2))
      (LB.LinComb (abelian₂ B₀ M₀) (K := Fin 8 × Fin 8) (fun p => sharpPair ρ Q D pr p.1 p.2 ≫ β₂)
        (fun p => W p.1 p.2)) :=
    LBIso.chartPull (chartPullLinComb (abelian₂ B₀ M₀) β₂ _ _ _ (𝟙 _) fun p => (Category.id_comp _).symm)
      (chartPullId _) ((GlobalTheory.PrimNorm.lbIso_iff hLam₀ _ _ _ _).2 rfl)
  have hN₁ := DVR.linComb_isLB (abelian₂ Q.B Q.M.L) hLam (fun p : Fin 8 × Fin 8 => sharpPair ρ Q D pr p.1 p.2)
    (fun p => W p.1 p.2)
  have hN₂ := DVR.linComb_isLB _ (pull_isLB hLam₀ β₂) (fun p : Fin 8 × Fin 8 => sharpPair ρ Q D pr p.1 p.2)
    (fun p => W p.1 p.2)
  have hN₃ := DVR.linComb_isLB (abelian₂ B₀ M₀) hLam₀ (fun p : Fin 8 × Fin 8 => sharpPair ρ Q D pr p.1 p.2 ≫ β₂)
    (fun p => W p.1 p.2)
  exact LBIso.trans D.P.isLB hS hN₃ ⟨w, hw⟩
    (LBIso.trans hS hN₁ hN₃ h₂.symm (LBIso.trans hN₁ hN₂ hN₃ h₃ h₄))

example {W₀ : Type} [CommRing W₀] (W : Matrix (Fin 8) (Fin 8) ℤ) (Q : Data V) (ρ : V →+* V₁) (D : DegPre V₁)
    (e : (Fin 8 → Q.X) ≃+ D.X) (τ₀ : Gens Q) (ib : W₀ →+* V) (h₁ : SharpRef W Q ρ D e) (h₂ : FromBase Q τ₀ ib) :
    ∃ (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B)) (B₀ : Over (Sp W₀)) (_ : GrpObj B₀)
      (_ : IsCommMonObj B₀) (M₀ : LB B₀.left) (β₂ : (G2 Q.B).left ⟶ (G2 B₀).left),
      LBIso D.P.L (LB.LinComb (abelian₂ B₀ M₀) (K := Fin 8 × Fin 8) (fun p => sharpPair ρ Q D pr p.1 p.2 ≫ β₂)
        (fun p => W p.1 p.2)) := by
  obtain ⟨pr, w, -, -, hw, -, -⟩ := h₁
  obtain ⟨B₀, iG, iC, M₀, -, -, -, β₂, w₀, -, hM₀, -, -, hw₀, -, -, -⟩ := h₂
  exact ⟨pr, B₀, iG, iC, M₀, β₂, sharp_bundle W ρ Q D pr w hw B₀ M₀ hM₀ β₂ w₀ hw₀⟩

end GlobalTheory.Poinc.Sep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegPBOfFiniteEtaleCoverStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegPB_of_finite_etale_surjective_cover : ∀ (h n : ℕ) (B : Type) [CommRing B] (b : TBase B n) (S S₁ Y : Scheme.{0}) (s : S ⟶ Sp B) (s₁ : S₁ ⟶ Sp B) (sY : Y ⟶ Sp B) (c : SiegPre h n (b.ζ : B) s) (c₁ : SiegPre h n (b.ζ : B) s₁) (u : SiegPre h n (b.ζ : B) sY) (p : S₁ ⟶ S) (f : S ⟶ Y), 3 ≤ n → Odd n → u.Principal → IsFinite p → Etale p → Surjective p → SiegPB c₁ c p → SiegPB c₁ u (p ≫ f) → SiegPB c u f := by
  first | exact @GlobalTheory.siegPB_of_finite_etale_cover | exact GlobalTheory.siegPB_of_finite_etale_cover | (intros; apply GlobalTheory.siegPB_of_finite_etale_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifiedOfFaithfullyFlat
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegFpqcDesc

open GlobalTheory.SiegPBDescent GlobalTheory.SiegelPullComp

variable {h n : ℕ} {B B' B₁ : Type} [CommRing B] [CommRing B'] [CommRing B₁] {ζ' : B'} {ζ₁ : B₁}
  {T T₁ : Scheme.{0}} {s₁ : T₁ ⟶ Sp B₁}

theorem siegPB_id_of_fpqc (b : TBase B n) {sc : T ⟶ Sp B'} {su : T ⟶ Sp B} (c : SiegPre h n ζ' sc)
    (u : SiegPre h n (b.ζ : B) su) (c₁ : SiegPre h n ζ₁ s₁) (p : T₁ ⟶ T) [Flat p] [QuasiCompact p] [Surjective p]
    (hn : 3 ≤ n) (ho : Odd n) (hu : u.Principal) (m : SiegPB c₁ c p) (k : SiegPB c₁ u p) : SiegPB c u (𝟙 T) := by
  obtain ⟨φ₁, hm⟩ := exists_of_siegPB m
  obtain ⟨ψ₁, hk⟩ := exists_of_siegPB k
  obtain ⟨φ₁₂, hφ, sq₁, iso₁, lev₁⟩ := (sRelBy_one_iff _ _ _ _).1 hm
  obtain ⟨ψ₁₂, hψ, sq₂, iso₂, lev₂⟩ := (sRelBy_one_iff _ _ _ _).1 hk
  have : Epi p := Flat.epi_of_flat_of_surjective p
  have : Flat φ₁ := MorphismProperty.of_isPullback hφ.1.flip inferInstance
  have : Surjective φ₁ := MorphismProperty.of_isPullback hφ.1.flip inferInstance
  have : QuasiCompact φ₁ := MorphismProperty.of_isPullback hφ.1.flip inferInstance
  have : Flat ψ₁ := MorphismProperty.of_isPullback hψ.1.flip inferInstance
  have : Surjective ψ₁ := MorphismProperty.of_isPullback hψ.1.flip inferInstance
  have : QuasiCompact ψ₁ := MorphismProperty.of_isPullback hψ.1.flip inferInstance
  have : EffectiveEpi φ₁ := inferInstance
  have : EffectiveEpi ψ₁ := inferInstance
  let φ := EffectiveEpi.desc φ₁ ψ₁ (comp_eq_of_comp_eq b hn ho hu hm hk)
  have hφψ : φ₁ ≫ φ = ψ₁ := EffectiveEpi.fac _ _ _
  have w : φ ≫ u.A.hom = c.A.hom := by
    rw [← cancel_epi φ₁, ← Category.assoc, hφψ, hψ.1.w, hφ.1.w]
  have : Mono φ := mono_of_fac hφ.1 hψ.1 hφψ w
  let ψ := EffectiveEpi.desc ψ₁ φ₁ (fun g₁ g₂ e => by
    rw [← cancel_mono φ, Category.assoc, Category.assoc, hφψ]; exact e)
  have hψφ : ψ₁ ≫ ψ = φ₁ := EffectiveEpi.fac _ _ _
  have : IsIso φ := ⟨ψ, by rw [← cancel_epi φ₁, ← Category.assoc, hφψ, hψφ, Category.comp_id],
    by rw [← cancel_epi ψ₁, ← Category.assoc, hψφ, hφψ, Category.comp_id]⟩
  have gp : IsGrpPullback c.A u.A (𝟙 T) φ :=
    GlobalTheory.ObjDescent.isGrpPullback_id hφ hψ φ hφψ (w.trans (Category.comp_id _).symm)
  obtain ⟨φ₂, sq⟩ := GlobalTheory.SiegDesc.exists_isSquare gp.1.w
  have lev : ∀ a, (c.lev a).left ≫ φ = 𝟙 T ≫ (u.lev a).left := fun a => by
    rw [Category.id_comp, ← cancel_epi p, ← Category.assoc, ← lev₁ a, Category.assoc, hφψ, lev₂ a]
  have he : eSec (G2 c.A) ≫ φ₂ = eSec (G2 u.A) := by
    have e₀ : eSec c.A ≫ φ = 𝟙 _ ≫ eSec u.A := (cubeMapOf gp).e_comm
    rw [Category.id_comp] at e₀
    apply pullback.hom_ext
    · show (eSec (G2 c.A) ≫ φ₂) ≫ (fst u.A u.A).left = eSec (G2 u.A) ≫ (fst u.A u.A).left
      rw [Category.assoc, sq.1, ← Category.assoc, eSec_fst, eSec_fst, e₀]
    · show (eSec (G2 c.A) ≫ φ₂) ≫ (snd u.A u.A).left = eSec (G2 u.A) ≫ (snd u.A u.A).left
      rw [Category.assoc, sq.2, ← Category.assoc, eSec_snd, eSec_snd, e₀]
  have hiso : LBIso c.P (u.P.pull φ₂) := by
    have h₁ := c.isLB
    have h₂ := pull_isLB u.isLB φ₂
    have hN := LB.isLB_div h₂ h₁
    have cN : CechPic.cls _ hN = CechPic.pull φ₂ (CechPic.cls _ u.isLB) - CechPic.cls _ h₁ :=
      CechPic.cls_div h₂ h₁ hN
    have hsq := GlobalTheory.SiegDesc.isPullback_of_isSquare hφ.1 sq₁
    have e₂ : φ₁₂ ≫ φ₂ = ψ₁₂ := GlobalTheory.SiegDesc.isSquare_comp hφψ sq₁ sq sq₂
    have cl₁ : CechPic.cls c₁.P c₁.isLB = CechPic.pull φ₁₂ (CechPic.cls c.P c.isLB) :=
      (CechPic.cls_eq_iff _ (pull_isLB c.isLB _)).2 iso₁
    have cl₂ : CechPic.cls c₁.P c₁.isLB = CechPic.pull ψ₁₂ (CechPic.cls u.P u.isLB) :=
      (CechPic.cls_eq_iff _ (pull_isLB u.isLB _)).2 iso₂
    refine GlobalTheory.exists_gen_of_rigidified_of_flat_baseChange GlobalTheory.abelianSchemeLaws_all.1.globalFns T T₁ p (G2 c.A) _
      (AbelianSchemeGerms.isAbelianScheme_tensor _ _ c.ab c.ab) hN inferInstance inferInstance inferInstance
      ((CechPic.cls_eq_zero_iff (pull_isLB hN _)).1 ?_) ((CechPic.cls_eq_zero_iff (pull_isLB hN _)).1 ?_)
    · rw [CechPic.cls_pull hN, cN, map_sub, ← CechPic.pull_comp, he, cls_eSec u, cls_eSec c, sub_zero]
    · rw [CechPic.cls_pull hN, cN, ← hsq.isoPullback_inv_fst, CechPic.pull_comp, map_sub, ← CechPic.pull_comp, e₂,
        ← cl₂, ← cl₁, sub_self, map_zero]
  exact siegPB_of ((sRelBy_one_iff _ _ _ _).2 ⟨φ₂, gp, sq, hiso, lev⟩)

theorem siegPB_of_fpqc_cover (h n : ℕ) (B : Type) [CommRing B] (b : TBase B n) (S S₁ Y : Scheme.{0})
    (s : S ⟶ Sp B) (s₁ : S₁ ⟶ Sp B) (sY : Y ⟶ Sp B) (c : SiegPre h n (b.ζ : B) s) (c₁ : SiegPre h n (b.ζ : B) s₁)
    (u : SiegPre h n (b.ζ : B) sY) (p : S₁ ⟶ S) (f : S ⟶ Y) (hn : 3 ≤ n) (ho : Odd n) (hu : u.Principal)
    [Flat p] [QuasiCompact p] [Surjective p] (m : SiegPB c₁ c p) (k : SiegPB c₁ u (p ≫ f)) : SiegPB c u f := by
  obtain ⟨⟨u', hu'⟩, hpr⟩ := GlobalTheory.siegPre_pullback h n B (b.ζ : B) Y S sY (f ≫ sY) f u rfl
  have k' : SiegPB c₁ u' p := pb_cancel hu' k
  have e := pb_comp hu' (siegPB_id_of_fpqc b c u' c₁ p hn ho (hpr u' hu' hu) m k')
  rwa [Category.id_comp] at e

theorem classified_of_faithfullyFlat : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] [Module.FaithfullyFlat R R'] (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → (∀ c' : SiegPre g n (zetaAway n) (spMap ((algebraMap R R').comp β)), SiegPB c' c (spMap (algebraMap R R')) → ∃ f : Sp R' ⟶ F.X, f ≫ F.s = spMap ((algebraMap R R').comp β) ∧ SiegPB c' F.univ f) → ∃ f : Sp R ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  intro g n hg hn ho F R R' _ _ _ _ β c _ H
  have hn0 : n ≠ 0 := by omega
  let π : Sp R' ⟶ Sp R := spMap (algebraMap R R')
  have : Flat π := Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have : Surjective π := ⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat⟩
  have : QuasiCompact π := inferInstance
  have hcomp : π ≫ spMap β = spMap ((algebraMap R R').comp β) := by
    simp only [π, spMap, ← Spec.map_comp]
    rfl
  obtain ⟨⟨c', hc'⟩, -⟩ := GlobalTheory.siegPre_pullback g n (cycAway n) (zetaAway n) (Sp R) (Sp R') (spMap β)
    (spMap ((algebraMap R R').comp β)) π c hcomp
  obtain ⟨f', hf's, hf'⟩ := H c' hc'
  have hagree : pullback.fst π π ≫ f' = pullback.snd π π ≫ f' := by
    obtain ⟨⟨c₁, hc₁⟩, -⟩ := GlobalTheory.siegPre_pullback g n (cycAway n) (zetaAway n) (Sp R') (pullback π π)
      (spMap ((algebraMap R R').comp β)) (pullback.fst π π ≫ spMap ((algebraMap R R').comp β))
      (pullback.fst π π) c' rfl
    have a₁ : SiegPB c₁ F.univ (pullback.fst π π ≫ f') := pb_comp hf' hc₁
    have b₁ : SiegPB c₁ c (pullback.fst π π ≫ π) := pb_comp hc' hc₁
    rw [pullback.condition] at b₁
    have b₂ : SiegPB c₁ c' (pullback.snd π π) := pb_cancel hc' b₁
    have a₂ : SiegPB c₁ F.univ (pullback.snd π π ≫ f') := pb_comp hf' b₂
    refine GlobalTheory.T.siegelFamily_classifyingMap_unique g n hg hn ho F _ _ c₁ _ _ (by rw [Category.assoc, hf's]) ?_ a₁ a₂
    rw [Category.assoc, hf's, ← hcomp, ← Category.assoc, ← pullback.condition, Category.assoc]
  have : IsRegularEpi π := isRegularEpi_of_flat_of_surjective_of_isAffine π
  let f := EffectiveEpi.desc π f' (fun g₁ g₂ e => by
    have := congrArg (pullback.lift g₁ g₂ e ≫ ·) hagree
    rwa [← Category.assoc, ← Category.assoc, pullback.lift_fst, pullback.lift_snd] at this)
  have hf : π ≫ f = f' := EffectiveEpi.fac _ _ _
  have : Epi π := Flat.epi_of_flat_of_surjective π
  refine ⟨f, ?_, ?_⟩
  · rw [← cancel_epi π, ← Category.assoc, hf, hf's, hcomp]
  · exact siegPB_of_fpqc_cover g n (cycAway n) (cycBase hn0) (Sp R) (Sp R') F.X (spMap β) _ F.s c c' F.univ π f
      hn ho F.princ hc' (by rw [hf]; exact hf')

end GlobalTheory.SiegFpqcDesc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFibrePowerPointEqOfMatchingLowerData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

theorem GlobalTheory.TInj.low_eq_of_match : ∀ {o : Type} [CommRing o] {ζ : o} {n : ℕ} (L : LowBase ζ n), 3 ≤ n → IsUnit ζ → IsUnit (n : o) → ∀ {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin L.T.r → ℤ)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D₁ D₂ : DegPre V) (ω₁ : L.W →+* V) (s₁ : I → V) (e₁ : D₁.X ≃+ (Fin L.T.r → ℤ)) (β₁ : D₁.P.A.left ⟶ L.T.B.left) (ββ₁ : (G2 D₁.P.A).left ⟶ (G2 L.T.B).left) (w₁ : LB.Iso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ L.T.B L.T.M.L).pull ββ₁)) (ω₂ : L.W →+* V) (s₂ : I → V) (e₂ : D₂.X ≃+ (Fin L.T.r → ℤ)) (β₂ : D₂.P.A.left ⟶ L.T.B.left) (ββ₂ : (G2 D₂.P.A).left ⟶ (G2 L.T.B).left) (w₂ : LB.Iso (abelian₂ D₂.P.A D₂.P.L) ((abelian₂ L.T.B L.T.M.L).pull ββ₂)) (b : D₁.P.A ⟶ D₂.P.A) (φ : D₁.X ≃+ D₂.X) (F : Type) [Field F] [Algebra (FractionRing V) F], D₁.TauBimult → D₂.TauBimult → From L.T ω₁ s₁ ε n D₁ e₁ β₁ ββ₁ w₁ → From L.T ω₂ s₂ ε n D₂ e₂ β₂ ββ₂ w₂ → ω₁.comp L.T.b = ω₂.comp L.T.b → Match D₁ D₂ b φ F → (∀ y, e₂ (φ y) = e₁ y) → (∀ a : Fin L.T.r → ℤ, ∃ (p₁ : QkPt D₁ F n) (p₂ : QkPt D₂ F n), p₁.y = e₁.symm a ∧ TautPt L.T ω₁ s₁ ε n D₁ e₁ β₁ ββ₁ w₁ F a p₁.g ∧ p₂.y = e₂.symm a ∧ TautPt L.T ω₂ s₂ ε n D₂ e₂ β₂ ββ₂ w₂ F a p₂.g ∧ QImg b φ p₁ p₂) → (∀ l : Fin L.h ⊕ Fin L.h → ℤ, ∃ (p₁ : QkPt D₁ F n) (p₂ : QkPt D₂ F n), p₁.y = 0 ∧ p₁.g.b.left ≫ β₁ ≫ L.β = (TF (R := V) F).hom ≫ spMap ω₁ ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom ≫ (L.F.univ.lev l).left ∧ p₂.y = 0 ∧ p₂.g.b.left ≫ β₂ ≫ L.β = (TF (R := V) F).hom ≫ spMap ω₂ ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom ≫ (L.F.univ.lev l).left ∧ QImg b φ p₁ p₂) → spMap ω₁ ≫ L.u = spMap ω₂ ≫ L.u ∧ (ω₁ = ω₂ → b.left ≫ β₂ = β₁) := by
  intro o _ ζ n L hn hζ hnu I _ ε V _ _ _ D₁ D₂ ω₁ s₁ e₁ β₁ ββ₁ w₁ ω₂ s₂ e₂ β₂ ββ₂ w₂ b φ F _ _ hτ₁ hτ₂ hF₁ hF₂ hω hM he
    hco hlev
  have himg : ∀ (p₁ : QkPt D₁ F n) (p₂ : QkPt D₂ F n), QImg b φ p₁ p₂ → p₂.y = φ p₁.y →
      p₂.g.b.left = p₁.g.b.left ≫ b.left := by
    rintro p₁ p₂ ⟨p', hp'y, hact, heqv⟩ hy
    have hg : p'.g = p₂.g := GlobalTheory.T.torsionPoint_torusPart_eq_of_equiv_same_lattice V D₂ hτ₂ F n (by omega) p' p₂ (hp'y.trans hy.symm) heqv
    rw [← hg, hact.1, Over.comp_left]
  haveI := hM.2.1
  haveI : IsMonHom (asIso b).hom := hM.1
  set t₁ : Sp V ⟶ L.F.X := spMap ω₁ ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom with ht₁
  set t₂ : Sp V ⟶ L.F.X := spMap ω₂ ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom with ht₂
  let a₁ : D₁.P.A.left ⟶ L.F.univ.A.left := β₁ ≫ L.β
  let a₂ : D₁.P.A.left ⟶ L.F.univ.A.left := b.left ≫ β₂ ≫ L.β
  let bb : (G2 D₁.P.A).left ⟶ (G2 D₂.P.A).left :=
    (lift (fst D₁.P.A D₁.P.A ≫ b) (snd D₁.P.A D₁.P.A ≫ b) : G2 D₁.P.A ⟶ G2 D₂.P.A).left
  let aa₁ : (G2 D₁.P.A).left ⟶ (G2 L.F.univ.A).left := ββ₁ ≫ L.β₂
  let aa₂ : (G2 D₁.P.A).left ⟶ (G2 L.F.univ.A).left := bb ≫ ββ₂ ≫ L.β₂
  have hpb₁ : IsGrpPullback D₁.P.A L.F.univ.A t₁ a₁ := IsGrpPullback.comp hF₁.1 L.cart
  have hpb₂ : IsGrpPullback D₁.P.A L.F.univ.A t₂ a₂ :=
    (IsGrpPullback.comp (ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_of_iso (asIso b))
      (IsGrpPullback.comp hF₂.1 L.cart)).congr (Category.id_comp _) rfl
  have hbsq : IsSquare b.left bb :=
    ⟨by rw [← Over.comp_left, lift_fst, Over.comp_left], by rw [← Over.comp_left, lift_snd, Over.comp_left]⟩
  have hsq₁ : IsSquare a₁ aa₁ := GlobalTheory.PolDeg.isSquare_comp hF₁.2.1 L.sq
  have hsq₂ : IsSquare a₂ aa₂ := GlobalTheory.PolDeg.isSquare_comp hbsq (GlobalTheory.PolDeg.isSquare_comp hF₂.2.1 L.sq)
  have hLam : ∀ D : DegPre V, (abelian₂ D.P.A D.P.L).IsLB := fun D => LB.isLB_linComb D.P.isLB _ _
  have hLamT : (abelian₂ L.T.B L.T.M.L).IsLB := LB.isLB_linComb L.T.M.isLB _ _
  have hU := L.F.univ.isLB
  have hA₁ : LBIso (abelian₂ D₁.P.A D₁.P.L) (L.F.univ.P.pull aa₁) :=
    LBIso.trans (hLam D₁) (pull_isLB hLamT ββ₁) (pull_isLB hU _) ⟨w₁, hF₁.2.2.1⟩
      (GlobalTheory.PolDeg.lbIso_pull_comp L.lb ββ₁ rfl)
  have hA₂' : LBIso (abelian₂ D₂.P.A D₂.P.L) (L.F.univ.P.pull (ββ₂ ≫ L.β₂)) :=
    LBIso.trans (hLam D₂) (pull_isLB hLamT ββ₂) (pull_isLB hU _) ⟨w₂, hF₂.2.2.1⟩
      (GlobalTheory.PolDeg.lbIso_pull_comp L.lb ββ₂ rfl)
  have hA₂ : LBIso (abelian₂ D₁.P.A D₁.P.L) (L.F.univ.P.pull aa₂) :=
    LBIso.trans (hLam D₁) (pull_isLB (hLam D₂) bb) (pull_isLB hU _) hM.2.2.1
      (GlobalTheory.PolDeg.lbIso_pull_comp hA₂' bb rfl)
  have hP : LBIso (L.F.univ.P.pull aa₁) (L.F.univ.P.pull aa₂) :=
    LBIso.trans (pull_isLB hU _) (hLam D₁) (pull_isLB hU _) hA₁.symm hA₂
  have hs : t₁ ≫ L.F.s = t₂ ≫ L.F.s := by
    have hb : spMap ω₁ ≫ spMap L.T.b = spMap ω₂ ≫ spMap L.T.b := by
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hω]
    have e : ∀ ω : L.W →+* V, (spMap ω ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom) ≫ L.F.s = spMap ω ≫ spMap L.T.b := by
      intro ω
      rw [Category.assoc, Category.assoc, ← L.u_base]
      rfl
    rw [ht₁, ht₂, e, e, hb]
  have hlev' : ∀ l, ∃ x : TF (R := V) F ⟶ D₁.P.A,
      x.left ≫ a₁ = (TF (R := V) F).hom ≫ t₁ ≫ (L.F.univ.lev l).left ∧
      x.left ≫ a₂ = (TF (R := V) F).hom ≫ t₂ ≫ (L.F.univ.lev l).left := by
    intro l
    obtain ⟨p₁, p₂, hy₁, hb₁, hy₂, hb₂, hQ⟩ := hlev l
    have h21 := himg p₁ p₂ hQ (by rw [hy₂, hy₁, map_zero])
    refine ⟨p₁.g.b, ?_, ?_⟩
    · simpa only [a₁, ht₁, Category.assoc] using hb₁
    · have : p₁.g.b.left ≫ a₂ = p₂.g.b.left ≫ β₂ ≫ L.β := by
        simp only [a₂, h21, Category.assoc]
      rw [this, hb₂]
      simp only [ht₂, Category.assoc]
  obtain ⟨ht, ha⟩ := GlobalTheory.T.eq_of_presentations_same_polarisation_level L.F hn hζ hnu V D₁.P.A t₁ t₂ a₁ a₂ aa₁ aa₂ hpb₁ hpb₂ hsq₁ hsq₂ hP hs F hlev'
  have hcoordEq : ∀ i, (spMap ω₁ ≫ L.u) ≫ (GlobalTheory.LowChart.coord L.F i).left =
      (spMap ω₂ ≫ L.u) ≫ (GlobalTheory.LowChart.coord L.F i).left := by
    intro i
    obtain ⟨p₁, p₂, hy₁, hT₁, hy₂, hT₂, hQ⟩ := hco (Pi.single i 1)
    have hφ : p₂.y = φ p₁.y := by
      rw [hy₂, hy₁]
      apply e₂.injective
      rw [he, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    have h21 := himg p₁ p₂ hQ hφ
    have c1 : (TF (R := V) F).hom ≫ (spMap ω₁ ≫ L.u) ≫ (GlobalTheory.LowChart.coord L.F i).left = p₁.g.b.left ≫ a₁ := by
      simp only [a₁, Category.assoc, ← L.coord i]
      rw [← Category.assoc p₁.g.b.left, hT₁.1]
      simp only [Category.assoc]
    have c2 : (TF (R := V) F).hom ≫ (spMap ω₂ ≫ L.u) ≫ (GlobalTheory.LowChart.coord L.F i).left = p₁.g.b.left ≫ a₂ := by
      simp only [a₂, Category.assoc, ← L.coord i]
      rw [← Category.assoc p₁.g.b.left, ← h21, ← Category.assoc p₂.g.b.left, hT₂.1]
      simp only [Category.assoc]
    have hgen : (TF (R := V) F).hom ≫ (spMap ω₁ ≫ L.u) ≫ (GlobalTheory.LowChart.coord L.F i).left =
        (TF (R := V) F).hom ≫ (spMap ω₂ ≫ L.u) ≫ (GlobalTheory.LowChart.coord L.F i).left := by
      rw [c1, c2, ha]
    have : IsProper L.F.univ.A.hom := L.F.univ.ab.proper
    haveI : IsDominant (TF (R := V) F).hom := ReciprocityTheory.ChartRestriction.G.DVR.GC.isDominant_jFR (V := V) F
    refine ext_of_isDominant_of_isSeparated L.F.univ.A.hom ?_ (TF (R := V) F).hom hgen
    simp only [Category.assoc, Over.w]
    exact ht
  refine ⟨GlobalTheory.LowChart.hom_ext _ _ (by simpa only [Category.assoc] using ht) hcoordEq, ?_⟩
  rintro rfl
  apply L.cart.1.hom_ext
  · simpa only [a₁, a₂, Category.assoc] using ha.symm
  · rw [Category.assoc, hF₂.1.1.w, ← Category.assoc, Over.w b, hF₁.1.1.w]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOfIsFiniteOfDimEqAbelianVarietyHomStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_of_isFinite_of_dim_eq_abelianVarietyHom : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), A.dim = B.dim → IsFinite f.hom.left → Surjective f.hom.left := by
  first | exact @GlobalTheory.AV.AbVar.surjective_of_isFinite_of_dim_eq | exact GlobalTheory.AV.AbVar.surjective_of_isFinite_of_dim_eq | (intros; apply GlobalTheory.AV.AbVar.surjective_of_isFinite_of_dim_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricCoordinatesO1FactorialPowerStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetric_coordinates_O1_factorial_power : ∀ (k Ω o : Type) [CommRing k] [Field Ω] [Algebra k Ω] [CommRing o] (M : RatModel k Ω) (n : ℕ) (h : M.Z ⟶ PSpace k n) (g : M.Z ⟶ PSpace o n) (c : Fin (n + 1) → Ω), PCrd (M.pt ≫ h) c → PCrd (M.pt ≫ g) (symTup c) → LBIso ((ProjSpace.O1 o n).pull g) (lbPow ((ProjSpace.O1 k n).pull h) (n + 1).factorial) := by
  first | exact @GlobalTheory.UMin.CrdSym.lbIso_symTup | exact GlobalTheory.UMin.CrdSym.lbIso_symTup | (intros; apply GlobalTheory.UMin.CrdSym.lbIso_symTup <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricPrincipalPolarisationExtendsSemiAbelianStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricPrincipalPolarisation_extends_semiAbelian : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∃ L₁ : LB G.left, L₁.IsLB ∧ LBIso (L₁.pull (pullback.fst G.hom (jK R))) (A.L.pull gen.hom.left) := by
  first | exact @GlobalTheory.SymExtend.main | exact GlobalTheory.SymExtend.main | (intros; apply GlobalTheory.SymExtend.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TailWeightLineNefStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tail_weight_line_nef : GlobalTheory.Published.SemiAbelianLieSeminegative → GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.NefNumerics → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∀ (τ : Psi H) (k : ℕ), Dw.p ≤ k → k + 1 < Dw.p + Dw.q → letI := algebraΓOfHom (str₀ TF.X Z); IsNef c.F (L₀ TF.X Z (GlobalTheory.NefWt.tailWt τ k)) := by
  first | exact @GlobalTheory.NefStep.isNef_tailWt | exact GlobalTheory.NefStep.isNef_tailWt | (intros; apply GlobalTheory.NefStep.isNef_tailWt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegenerationTauBalancedOfAdjointIntMatriceStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorDegeneration_tauBalanced_of_adjointIntMatrices : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (A A' : Matrix (Fin r) (Fin r) ℤ), A.transpose * (W + W.transpose) = (W + W.transpose) * A' → D'.toPre.TauBal (GlobalTheory.TensAct.matAct T A) (GlobalTheory.TensAct.matAct T A') (GlobalTheory.TensAct.latAct T A) (GlobalTheory.TensAct.latAct T A') := by
  first | exact @GlobalTheory.TensBal.tauBal_tens | exact GlobalTheory.TensBal.tauBal_tens | (intros; apply GlobalTheory.TensBal.tauBal_tens <;> assumption)
end

