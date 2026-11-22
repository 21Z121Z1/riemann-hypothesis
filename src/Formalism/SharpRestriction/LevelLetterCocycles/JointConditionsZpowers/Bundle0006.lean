import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseFont
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0004
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.LiftingConditionOfWindows
section
noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

open NumberField IsDedekindDomain

theorem locC_rTwO (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : D.nd.X i) :
    Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x) =
      twistM (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)) (Formalism.MainNotions.TruncatedSeriesCountingIdentities.chi1C C)⁻¹ := by
  apply MonoidHom.ext
  intro g
  apply Matrix.ext
  intro a b
  have key : ∀ u v : D.nd.O i, C.inc ((D.nbr i w hw).toLL (u * v)) =
      C.inc ((D.nbr i w hw).toLL u) * C.inc ((D.nbr i w hw).toLL v) := by
    intro u v
    rw [map_mul, map_mul]
  exact key _ _

theorem LiftWin_of (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw) (M h : ℕ)
    (hFont : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) (hG2 : Formalism.MainNotions.TruncatedSeriesCountingIdentities.admG2 (D := D) i r ρ π)
    (hc : ∀ x v, Continuous fun g => (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x) g).mulVec v)
    (hwin : ∀ x τ, JumpsInV (Br.PD D.loc D.nbr i w hw) (matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) τ
      (Set.Icc (-(M : ℤ)) h)) : LiftWin D i r w hw C M h := by
  intro T hT
  refine subquot_crys (fun x => Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x)) hc (hFont w hw C) (fun x => ?_) hwin T hT
  rw [locC_rTwO]
  exact (hG2 w hw C).2 x

theorem locC_cont (D : D7) (i : D.nd.Loc) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (hM : Continuous fun g => M g)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw) (v : Fin k → ↥C.LL.1) :
    Continuous fun g => (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C M g).mulVec v := by
  have hmat : Continuous fun g => Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C M g := by
    refine continuous_matrix fun a b => ?_
    have h1 : Continuous fun g : Br.G D.nbr i w hw => M ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) a b :=
      (hM.matrix_elem a b).comp (continuous_subtype_val.comp (Br.iota_cont D.nbr i w hw))
    have h2 : Continuous fun y : D.nd.O i => (((D.nbr i w hw).eO y : ↥(OL (D.nbr i w hw).LL)) :
        ↥(D.nbr i w hw).LL.1) := continuous_subtype_val.comp (D.nbr i w hw).eO_cont
    have h3 : Continuous fun y : ↥(D.nbr i w hw).LL.1 => C.inc y :=
      Continuous.subtype_mk continuous_subtype_val _
    exact h3.comp (h2.comp h1)
  exact hmat.matrix_mulVec continuous_const

theorem rTwO_cont (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (hr : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (x : D.nd.X i) : Continuous fun g => rTwO D.nd i r x g := by
  have h1 : Continuous fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i) := by
    have e : (fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i)) =
        fun g => ((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := by
      funext g
      rw [map_inv]
      rfl
    rw [e]
    exact (D.nd.chi_cont i 1).comp continuous_inv
  exact h1.smul (hr x)

theorem lifting_condition_of_windows (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.Decl D i)
    (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (M h : ℕ) (CA CB CK : ℝ) (hCA : 0 ≤ CA)
    (h54 : Formalism.MainNotions.LiftingTheory.LiftTheoremAllCases D HW F CA CB CK) (hl : D.nd.l i ≠ 2)
    (hur : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), w ∈ dc.col →
      (D.nbr i w hw).Kw.1 ≤ MaximalUnramifiedExtension (D.nd.l i))
    (hFont : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) (hG2 : Formalism.MainNotions.TruncatedSeriesCountingIdentities.admG2 (D := D) i r ρ π)
    (hr : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r)
    (hwin : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), w ∈ dc.col →
      ∀ C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw, C.IsGood → ∀ x τ,
        JumpsInV (Br.PD D.loc D.nbr i w hw) (matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) τ
          (Set.Icc (-(M : ℤ)) h))
    (he : ∀ w ∈ dc.col, CA * (1 + ((M + h : ℕ) : ℝ) / (D.nd.l i : ℝ) +
      (1 + Real.logb (D.nd.l i) (((M + h : ℕ) : ℝ) + 1))) ≤ (e' w : ℝ)) :
    Formalism.MainNotions.TruncatedSeriesCountingIdentities.LiftExponentAtPlaces (D := D) i r dc e' :=
  lifting_condition_of_crystalline_lift D HW F i r dc e' M h CA CB CK hCA h54 hl hur
    (fun w hw hcol C hC => LiftWin_of D i r ρ π w hw C M h hFont hG2
      (fun x v => locC_cont D i _ (rTwO_cont D i r hr x) w hw C v) (hwin w hw hcol C hC)) he

end Formalism.MainNotions.N
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.LocalInputFourteenOfLocal
section
noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions

theorem local_input_one_of_local (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h56 : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) :
    Formalism.MainNotions.LiftingTheory.adm1 D HW F := by
  unfold Formalism.MainNotions.LiftingTheory.adm1
  exact Formalism.MainNotions.DeltaInvariantLattices.wach_free_of_properties (first_clause_of_local_package D HW F Cm h56)

theorem local_input_two_of_local (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h56 : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) :
    Formalism.MainNotions.LiftingTheory.adm2 D HW F := by
  unfold Formalism.MainNotions.LiftingTheory.adm2
  exact second_clause_of_local_package D HW F Cm h56

theorem local_input_three_of_local (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h56 : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) :
    Formalism.MainNotions.LiftingTheory.adm3 D HW F Cm := by
  unfold Formalism.MainNotions.LiftingTheory.adm3
  exact third_clause_of_local_package D HW F Cm h56

theorem local_input_four_of_local (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h56 : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) :
    Formalism.MainNotions.LiftingTheory.ArchimedeanSignatureMatching D HW F Cm := by
  unfold Formalism.MainNotions.LiftingTheory.ArchimedeanSignatureMatching
  exact fourth_clause_of_local_package D HW F Cm h56

theorem local_input_five_of_local (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h56 : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) :
    Formalism.MainNotions.LiftingTheory.adm5 D HW F := by
  unfold Formalism.MainNotions.LiftingTheory.adm5
  exact fifth_clause_of_local_package D HW F Cm h56

theorem local_input_six_of_local (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h56 : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) :
    Formalism.MainNotions.LiftingTheory.adm6 D HW F := by
  unfold Formalism.MainNotions.LiftingTheory.adm6
  exact sixth_clause_of_local_package D HW F Cm h56

theorem local_input_seven_of_local (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h56 : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) :
    Formalism.MainNotions.LiftingTheory.adm7 D HW F := by
  unfold Formalism.MainNotions.LiftingTheory.adm7
  exact seventh_clause_of_local_package D HW F Cm h56

theorem local_input_eight_of_local (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h56 : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) :
    Formalism.MainNotions.LiftingTheory.adm8 D HW F := by
  unfold Formalism.MainNotions.LiftingTheory.adm8
  exact eighth_clause_of_local_package D HW F Cm h56

theorem local_input_nine_of_local (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h56 : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) :
    Formalism.MainNotions.LiftingTheory.adm9 D HW F := by
  unfold Formalism.MainNotions.LiftingTheory.adm9
  exact delta_invariants_of_local_package D HW F Cm h56

theorem local_input_ten_of_local (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h56 : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) :
    Formalism.MainNotions.LiftingTheory.adm10 D HW F := by
  unfold Formalism.MainNotions.LiftingTheory.adm10
  exact Formalism.MainNotions.DeltaInvariantLattices.wach_characterisation_of_tenth (tenth_clause_of_local_package D HW F Cm h56)

theorem local_input_eleven_of_local (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h56 : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) :
    Formalism.MainNotions.LiftingTheory.adm11 D HW F := by
  unfold Formalism.MainNotions.LiftingTheory.adm11
  exact Formalism.MainNotions.DeltaInvariantLattices.gamma_semisimple_local_of_consequences (consistency_of_local_package D HW F Cm h56)

theorem local_input_twelve_of_local (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h56 : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) :
    Formalism.MainNotions.LiftingTheory.adm12 D HW F := by
  unfold Formalism.MainNotions.LiftingTheory.adm12
  exact second_first_of_local_package D HW F Cm h56

theorem local_input_thirteen_of_local (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h56 : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) :
    Formalism.MainNotions.LiftingTheory.adm13 D HW F := by
  unfold Formalism.MainNotions.LiftingTheory.adm13
  exact second_b_of_local_package D HW F Cm h56

theorem local_input_fourteen_of_local (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h56 : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) :
    Formalism.MainNotions.LiftingTheory.adm14 D HW F := by
  unfold Formalism.MainNotions.LiftingTheory.adm14
  exact second_c_of_local_package D HW F Cm h56

theorem local_input_fifteen_of_local (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h56 : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) :
    Formalism.MainNotions.LiftingTheory.adm15 D HW F := by
  unfold Formalism.MainNotions.LiftingTheory.adm15
  exact second_dual_of_local_package D HW F Cm h56

theorem local_input_sixteen_of_local (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h56 : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) :
    Formalism.MainNotions.LiftingTheory.adm16 D HW F := by
  unfold Formalism.MainNotions.LiftingTheory.adm16
  exact lemma_three_of_local_package D HW F Cm h56

theorem class_map_naturality_of_herr (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h : Formalism.MainNotions.LocalSituation.ClassMapInjectiveBijectiveNorms D HW F) : Formalism.MainNotions.LiftingTheory.adm21 D HW F := by
  intro l _ K s LL hg
  obtain ⟨hA, -, hN⟩ := h l K s LL hg
  refine ⟨hN, fun _ hl => ?_⟩
  intro T T' f pr pr' hpr
  have h2 : Formalism.MainNotions.LocalSituation.ell (Formalism.MainNotions.LocalSituation.sit D.loc HW l (D.locA l) K s LL hg) = 2 →
      ∃ i : (Formalism.MainNotions.LocalSituation.sit D.loc HW l (D.locA l) K s LL hg).K, i ^ 2 = -1 := by
    intro h2
    exact absurd (((D.loc l).PD_p K).symm.trans h2) hl
  exact ((hA h2 T).2.2 T' f pr pr' hpr).symm

end Formalism.MainNotions.N
end
end

