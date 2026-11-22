import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0390
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0422
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0428
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralDefiniteQuotientEqClassSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepLevelContainsDeepCongruenceAtBadPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0475
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryAdelicSupportedAtBadPrimePlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0501
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0441
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0484
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0389
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0367
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0426
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0378
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0427
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0380
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0362
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0355

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticesSameSplitShapeCarriedByCentral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch

set_option maxHeartbeats 1000000 in

theorem sMoves_of_wShape : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S S₀ A Ln : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (o : OrthDec S₀ A Ln) (ζ : Fin Ln.rank → D.host.E) (L L' : Lat S) (N N' : Lat A) (α α' β β' : Fin ρ → k) (γ δ c₀ : k) (a₀ : GA D A), IsLineVec Ln ζ → IsSelfDualC S L → IsSelfDualC S L' → WShape p d o ζ L α α' γ 1 N → WShape p d o ζ L' β β' δ a₀ N' → latV A N (· = p.v) = latV A N' (· = p.v) → c₀ ≠ 0 → (∀ i, valuation k (β i * c₀) = valuation k (α i)) → (∀ i, valuation k (β' i * c₀) = valuation k (α' i)) → valuation k (δ * c₀) = valuation k γ → ∃ (a : GA D A) (c : AE D), CenAt A p.v a ∧ NormOneAt p.v c ∧ SMoves S c (embA d o (a₀ * a)) L L' p.v := by
  intro D k _ _ _ _ p S S₀ A Ln ρ d o ζ L L' N N' α α' β β' γ δ c₀ a₀ hζ hL hL' hW hW' hN hc₀ hb hb' hd
  obtain ⟨c, hc, hpc⟩ := GlobalTheory.T.exists_normOneIdele_with_splitPlace_component D k p c₀ hc₀
  obtain ⟨c', hc', hpc'⟩ := GlobalTheory.T.exists_normOneIdele_with_splitPlace_component D k p c₀⁻¹ (inv_ne_zero hc₀)
  obtain ⟨a, haC, ha⟩ := GlobalTheory.T.exists_centralUnitary_scalar_of_normOneIdele D A p.v c' hc'
  refine ⟨a, c, haC, hc, ?_⟩
  apply GlobalTheory.T.normOneHomothety_carries_selfDual_of_splitComponent D k p S L L' c _ hL hL' hc
  set f : D.host.E →+* k := p.pr.comp (incA D) with hf
  have hatW : ∀ {m n : ℕ} (X : Matrix (Fin m) (Fin n) D.host.E), atW p X = X.map f := fun _ => rfl
  have hrat : ∀ {m n : ℕ} (X : Matrix (Fin m) (Fin n) D.host.E), atW p X = (rat X).map p.pr := fun _ => rfl
  have hkey : ∀ {n m l : ℕ} (M : Matrix (Fin n) (Fin l) (AE D)) (R : Matrix (Fin l) (Fin m) (AE D))
      (u : Fin m → k), M.map p.pr *ᵥ (R.map p.pr *ᵥ u) = (M * R).map p.pr *ᵥ u := by
    intro n m l M R u; rw [Matrix.mulVec_mulVec, Matrix.map_mul]

  have hsum : atW p d.e * atW p d.qX + atW p d.i₀ * atW p d.q0 + atW p d.e' * atW p d.qY = 1 := by
    simp only [hatW]
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add f), ← Matrix.map_add _ (map_add f), d.sum_eq_one_rat,
      Matrix.map_one _ (map_zero f) (map_one f)]
  have hsumA : atW p o.iA * atW p o.qA + atW p o.iB * atW p o.qB = 1 := by
    simp only [hatW]
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add f), o.iA_qA_add, Matrix.map_one _ (map_zero f) (map_one f)]
  have hrk : Ln.rank = 1 := hζ.1
  have j0 : Fin Ln.rank := ⟨0, by omega⟩
  have huniq : ∀ j : Fin Ln.rank, j = j0 := fun j => Fin.ext (by have := j.2; have := j0.2; omega)
  have hζ0 : ζ j0 ≠ 0 := by
    intro h0
    apply hζ.2
    have : ζ = 0 := funext fun j => by rw [huniq j, h0]; rfl
    simp [this]
  have hfζ : f (ζ j0) ≠ 0 := fun h => hζ0 (f.injective (by rw [h, map_zero]))
  set ζk : Fin Ln.rank → k := fun j => f (ζ j) with hζk
  set zv : Fin S.rank → k := fun r' => p.pr (incA D ((d.i₀ *ᵥ vecB o ζ) r')) with hzv
  have hz : zv = atW p (d.i₀ * o.iB) *ᵥ ζk := by
    funext r
    simp only [hzv, vecB, Matrix.mulVec_mulVec]
    exact RingHom.map_mulVec f (d.i₀ * o.iB) ζ r
  have hdec : ∀ x : Fin S.rank → k, ∃ (x1 x2 : Fin ρ → k) (t : k) (y : Fin A.rank → k),
      x = atW p d.e *ᵥ x1 + atW p d.e' *ᵥ x2 + t • zv +
        atW p (d.i₀ * o.iA) *ᵥ ((Formalism.L2.Theta.mt A 1).map p.pr *ᵥ y) := by
   intro x
   set x0 := atW p d.q0 *ᵥ x
   set w := atW p o.qB *ᵥ x0
   set y := atW p o.qA *ᵥ x0
   set t := w j0 / f (ζ j0)
   have hw : w = t • ζk := by
     funext j; rw [huniq j]; simp only [Pi.smul_apply, smul_eq_mul, hζk, t]; field_simp
   have hx : x = atW p d.e *ᵥ (atW p d.qX *ᵥ x) + atW p d.e' *ᵥ (atW p d.qY *ᵥ x) + t • zv +
       atW p (d.i₀ * o.iA) *ᵥ ((Formalism.L2.Theta.mt A 1).map p.pr *ᵥ y) := by
     rw [mt_one, Matrix.map_one _ (map_zero p.pr) (map_one p.pr), Matrix.one_mulVec, hz, ← Matrix.mulVec_smul, ← hw]
     have hm : atW p d.i₀ * (atW p o.iA * atW p o.qA + atW p o.iB * atW p o.qB) * atW p d.q0 =
         atW p d.i₀ * atW p d.q0 := by rw [hsumA, Matrix.mul_one]
     have h0 : atW p (d.i₀ * o.iA) *ᵥ y + atW p (d.i₀ * o.iB) *ᵥ w = atW p d.i₀ *ᵥ x0 := by
       simp only [y, w, x0, hatW, Matrix.map_mul, Matrix.mulVec_mulVec, ← Matrix.add_mulVec]
       simp only [← hatW]
       rw [← hm]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
     calc x = (1 : Matrix (Fin S.rank) (Fin S.rank) k) *ᵥ x := (Matrix.one_mulVec x).symm
       _ = _ := by
         rw [← hsum, Matrix.add_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
           ← Matrix.mulVec_mulVec, ← h0]
         abel
   exact ⟨_, _, _, _, hx⟩
  intro x
  obtain ⟨x1, x2, t, y, rfl⟩ := hdec x
  rw [hW x1 x2 t y]
  have jX : rat d.e = d.jX := rfl
  have jY : rat d.e' = d.jY := rfl
  have jA : rat (d.i₀ * o.iA) = d.j0 * o.jA := rat_mul _ _
  have jB : rat (d.i₀ * o.iB) = d.j0 * o.jB := rat_mul _ _
  have hGX : Formalism.L2.Theta.mt S (embA d o (a₀ ⬝ a)) ⬝ d.jX = d.jX := d.wittDecomp_anisotropicEmbedding_inclX _
  have hGY : Formalism.L2.Theta.mt S (embA d o (a₀ ⬝ a)) ⬝ d.jY = d.jY := d.wittDecomp_anisotropicEmbedding_inclY _
  have hG0' : Formalism.L2.Theta.mt S (embA d o (a₀ ⬝ a)) ⬝ d.j0 = d.j0 ⬝ Formalism.L2.Theta.mt S₀ (o.emb (a₀ ⬝ a, 1)) :=
    d.wittDecomp_anisotropicEmbedding_inclAnisotropic _
  have hG0 : ∀ {m : ℕ} (R : Matrix (Fin S₀.rank) (Fin m) (AE D)), Formalism.L2.Theta.mt S (embA d o (a₀ ⬝ a)) ⬝ (d.j0 ⬝ R) =
      d.j0 ⬝ (Formalism.L2.Theta.mt S₀ (o.emb (a₀ ⬝ a, 1)) ⬝ R) := by
    intro m R; rw [← Matrix.mul_assoc, hG0', Matrix.mul_assoc]
  have hBB : Formalism.L2.Theta.mt S₀ (o.emb (a₀ ⬝ a, 1)) ⬝ o.jB = o.jB := by rw [o.emb_jB, mt_one, Matrix.mul_one]
  have hAA : Formalism.L2.Theta.mt S₀ (o.emb (a₀ ⬝ a, 1)) ⬝ o.jA = o.jA ⬝ (Formalism.L2.Theta.mt A a₀ ⬝ Formalism.L2.Theta.mt A a) := by
    rw [o.emb_jA, mt_mul]
  set G := Formalism.L2.Theta.mt S (embA d o (a₀ * a)) with hG
  have T1 : G.map p.pr *ᵥ (atW p d.e *ᵥ x1) = atW p d.e *ᵥ x1 := by rw [hrat, hkey, jX, hGX]
  have T2 : G.map p.pr *ᵥ (atW p d.e' *ᵥ x2) = atW p d.e' *ᵥ x2 := by rw [hrat, hkey, jY, hGY]
  have hz' : zv = (d.j0 ⬝ o.jB).map p.pr *ᵥ ζk := by
    rw [← jB]; exact hz
  have T3 : G.map p.pr *ᵥ zv = zv := by
    rw [hz', hkey, hG0, hBB]
  have hms : ∀ {m n : ℕ} (r : AE D) (X : Matrix (Fin m) (Fin n) (AE D)), (r • X).map p.pr = p.pr r • X.map p.pr := by
    intro m n r X; ext i j; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  have T4 : G.map p.pr *ᵥ (atW p (d.i₀ * o.iA) *ᵥ y) =
      c₀⁻¹ • (atW p (d.i₀ * o.iA) *ᵥ ((Formalism.L2.Theta.mt A a₀).map p.pr *ᵥ y)) := by
    rw [hrat, hkey, hkey, jA, hG0, hAA, ha, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_smul,
      hms, Matrix.smul_mulVec, hpc', Matrix.mul_assoc]
  have himg : p.pr c • (G.map p.pr *ᵥ (atW p d.e *ᵥ x1 + atW p d.e' *ᵥ x2 + t • zv +
      atW p (d.i₀ * o.iA) *ᵥ ((Formalism.L2.Theta.mt A 1).map p.pr *ᵥ y))) =
      atW p d.e *ᵥ (c₀ • x1) + atW p d.e' *ᵥ (c₀ • x2) + (c₀ * t) • zv +
        atW p (d.i₀ * o.iA) *ᵥ ((Formalism.L2.Theta.mt A a₀).map p.pr *ᵥ y) := by
    rw [mt_one, Matrix.map_one _ (map_zero p.pr) (map_one p.pr), Matrix.one_mulVec, Matrix.mulVec_add,
      Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, T1, T2, T3, T4, hpc]
    simp only [smul_add, Matrix.mulVec_smul, smul_smul, mul_inv_cancel₀ hc₀, one_smul]
  rw [himg, hW' (c₀ • x1) (c₀ • x2) (c₀ * t) y, hN]
  have hval : ∀ u u' z : k, valuation k (u * c₀) = valuation k u' → (u * (c₀ * z) ∈ 𝒪[k] ↔ u' * z ∈ 𝒪[k]) := by
    intro u u' z h
    rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff, ← mul_assoc, map_mul, h, ← map_mul]
  refine and_congr (forall_congr' fun i => (hval _ _ _ (hb i)).symm)
    (and_congr (forall_congr' fun i => (hval _ _ _ (hb' i)).symm) (and_congr (hval _ _ _ hd).symm Iff.rfl))

end GlobalTheory.Core.Mi.LatMatch

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelCharacterEqOneOfDeepAtSplitBadPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
open GlobalTheory.Mem.Col2.AdT
open Filter Topology

noncomputable section

open Formalism.L2.DIV Formalism.L2.Col Formalism.UG

namespace GlobalTheory.Mem.Col2.AdT.SplitChi

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]

theorem adAt_conjP_eq_one (hc : CMData F E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : J = 1) {u : GL (Fin n) (AfE F E)}
    (hu : u ∈ UPts hc.sig J (FiniteAdeleRing (𝓞 F) F)) (P : HeightOneSpectrum (𝓞 E))
    (hP : ∀ r s, adAt F P (u.1 r s) = (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) (r s : Fin n) :
    adAt F (conjPrime₂ P) (u.1 r s) = (1 : Matrix (Fin n) (Fin n) ((conjPrime₂ P).adicCompletion E)) r s := by
  subst hJ
  have hinv := GlobalTheory.Mem.Col2.AdT.Opn.inv_eq_cT hc.sig hu
  have h1 : (u : Matrix (Fin n) (Fin n) (AfE F E)) *
      (1 + cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) ((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1)) = 1 := by
    rw [← hinv, Units.mul_inv]
  have hC : (cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) ((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1)).map
      (adAt F (conjPrime₂ P)) = 0 := by
    refine Matrix.ext fun i j => ?_
    show adAt F (conjPrime₂ P) (sigR hc.sig (FiniteAdeleRing (𝓞 F) F) (((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1) j i)) = 0
    have e2 : adAt F P ((1 : Matrix (Fin n) (Fin n) (AfE F E)) j i) = (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) j i := by
      rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
    have hX : adAt F P (((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1) j i) = 0 := by
      rw [Matrix.sub_apply, map_sub, hP, e2, sub_self]
    have e := GlobalTheory.Mem.Col2.valued_sigR hc (conjPrime₂ P) (((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1) j i)
    rw [GlobalTheory.CharValCompare.conjP_conjP, hX, Valuation.map_zero] at e
    exact (Valuation.zero_iff _).1 e
  have h2 := congrArg (adAt F (conjPrime₂ P)).mapMatrix h1
  rw [map_mul, map_add, map_one] at h2
  change _ * (1 + (cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) ((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1)).map
      (adAt F (conjPrime₂ P))) = 1 at h2
  rw [hC, add_zero, mul_one] at h2
  exact congrFun (congrFun h2 r) s

theorem bc_prV_eq_one_of_split (hc : CMData F E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : J = 1) {u : GL (Fin n) (AfE F E)}
    (hu : u ∈ UPts hc.sig J (FiniteAdeleRing (𝓞 F) F)) (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F))
    (hover : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → w = P ∨ w = conjPrime₂ P)
    (hP : ∀ r s, adAt F P (u.1 r s) = (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) :
    bc (prV (E := E) v) u = 1 := by
  refine GlobalTheory.Mem.Col2.AdPlace.bc_prV_eq_one_of_adAt F E n v u fun w hw r s => ?_
  rcases hover w hw with rfl | rfl
  · rw [hP, Matrix.one_apply]
  · rw [adAt_conjP_eq_one hc hJ hu P hP r s, Matrix.one_apply]

end Gen

section Root

theorem exists_root_GL {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (m n : ℕ) (hn : 0 < n)
    (c : P.adicCompletion E) (hc : Valued.v c < 1) (A : GL (Fin m) (P.adicCompletion E))
    (hA : ∀ r s, Valued.v (A.1 r s - (1 : Matrix (Fin m) (Fin m) (P.adicCompletion E)) r s) ≤
      Valued.v ((n : P.adicCompletion E) ^ 2 * c)) :
    ∃ M : GL (Fin m) (P.adicCompletion E), M ^ n = A ∧
      ∀ r s, Valued.v (M.1 r s - (1 : Matrix (Fin m) (Fin m) (P.adicCompletion E)) r s) ≤ Valued.v ((n : P.adicCompletion E) * c) := by
  obtain ⟨M, hM1, hM2⟩ := GlobalTheory.MatNthRoot.exists_nthRoot E P m n c A.1 hn hc
    (fun r s => by rw [Matrix.sub_apply]; exact hA r s)
  have hu : IsUnit M := (isUnit_pow_iff hn.ne').1 (hM2 ▸ A.isUnit)
  obtain ⟨M, rfl⟩ := hu
  exact ⟨M, Units.ext (by rw [Units.val_pow_eq_pow_val, hM2]), fun r s => by rw [← Matrix.sub_apply]; exact hM1 r s⟩

end Root

section Fin

theorem chi_eq_one_of_pow {G : Type} [Group G] {U : Subgroup G} (χ : U →* ℂˣ) (x z : U) (n : ℕ) (hz : χ z ^ n = 1)
    (hy : χ ((z ^ n)⁻¹ * x) = 1) : χ x = 1 := by
  rw [map_mul, map_inv, map_pow, hz, inv_one, one_mul] at hy
  exact hy

theorem map_inv_pow_mul_eq_one {G H : Type} [Group G] [Group H] (f : G →* H) {x z : G} (n : ℕ) (hz : f z = 1) (hx : f x = 1) :
    f ((z ^ n)⁻¹ * x) = 1 := by
  rw [map_mul, map_inv, map_pow, hz, hx, one_pow, inv_one, one_mul]

end Fin

set_option maxHeartbeats 2000000 in

theorem chi_eq_one_of_deep : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (T i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) T (I.rec7 l Z).R.f bad) (n : ℕ), 0 < n → (∀ κ : S.U, S.chi κ ^ n = 1) → ∀ (P : SBof I a) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∃ N : ℕ, ∀ x : S.U, (∀ v', v' ≠ v → bc (prV (E := (I.rec7 l Z).host.E) v') x.1 = 1) → ∀ w : GL (Fin ((I.rec7 l Z).R.N i)) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) N w → bc (prV (E := (I.rec7 l Z).host.E) v) x.1 = bc (prV (E := (I.rec7 l Z).host.E) v) w → S.chi x = 1 := by
  intro B X I hI hPin l Z a T i hi bad S n hn hchi P v hv
  obtain ⟨N₀, hN₀⟩ := GlobalTheory.Mem.Col2.AdT.Opn.level_contains_deep I hI hPin l Z a T i hi bad S P v hv
  have hd := fun N z => GlobalTheory.Mem.Col2.AdT.AdelicValuationDictionary.main I hI l Z a ((I.rec7 l Z).R.N i) N P z
  obtain ⟨hs, hq, -⟩ := hd 0 1
  have hu : P.1.under (𝓞 B.host.F) = v := by
    rw [hs] at hv
    exact HeightOneSpectrum.ext (Eq.symm hv)
  haveI : CharZero (P.1.adicCompletion B.fields.E) := algebraRat.charZero _
  set c : P.1.adicCompletion B.fields.E := ((qOf P.1 : ℕ) : P.1.adicCompletion B.fields.E) ^ (N₀ + 1) with hcdef
  have hc : Valued.v c = WithZero.exp (-((N₀ : ℤ) + 1)) := by
    rw [hcdef, map_pow, hq, ← WithZero.exp_nsmul]
    congr 1
    simp
  have hc1 : Valued.v c < 1 := by
    rw [hc, ← WithZero.exp_zero]; exact WithZero.exp_lt_exp.2 (by omega)
  have hn1 : Valued.v (n : P.1.adicCompletion B.fields.E) ≤ 1 := GlobalTheory.MatNthRoot.v_natCast_le_one n
  have hε : Valued.v ((n : P.1.adicCompletion B.fields.E) ^ 2 * c) ≠ 0 := by
    rw [map_mul, hc]
    refine mul_ne_zero ?_ WithZero.exp_ne_zero
    rw [Valuation.ne_zero_iff]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 hn.ne')
  set e := WithZero.log (Valued.v ((n : P.1.adicCompletion B.fields.E) ^ 2 * c)) with he
  refine ⟨(-e).toNat, fun x hxv w hw hxw => ?_⟩

  have hxP : ∀ r s, adAt B.host.F P.1 (x.1.1 r s) = adAt B.host.F P.1 (w.1 r s) := fun r s => by
    have h := congrArg (fun g : GL (Fin ((I.rec7 l Z).R.N i)) _ => g.1 r s) hxw
    refine GlobalTheory.Mem.Col2.AdT.LocSplice.adAt_eq_of_prV P.1 ?_
    rw [hu]
    exact h
  have hwP := ((hd _ w).2.2).1 hw
  have hwP := ((hd (-e).toNat w).2.2).1 hw
  have hA : ∀ r s, Valued.v (adAt B.host.F P.1 (x.1.1 r s) - (1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (P.1.adicCompletion B.fields.E)) r s) ≤
      Valued.v ((n : P.1.adicCompletion B.fields.E) ^ 2 * c) := fun r s => by
    rw [hxP]
    refine (hwP r s).trans ?_
    rw [← WithZero.exp_log hε, ← he]
    exact WithZero.exp_le_exp.2 (by omega)
  let x' : GlobalTheory.Mem.Col2.TC.GA B (B.R.N i) := x.1
  obtain ⟨Mu, hMun, hMu1⟩ := exists_root_GL P.1 (B.R.N i) n hn c hc1
    (Matrix.GeneralLinearGroup.map (adAt B.host.F P.1) x') hA
  obtain ⟨z, hzU, hzv, hzP⟩ := GlobalTheory.Mem.Col2.AdLift.exists_lift I hI hPin l Z a i hi P v hv Mu
  have hz : z ∈ S.U := hN₀ z hzU hzv (((hd N₀ z).2.2).2 fun r s => by
    rw [hzP]
    refine (hMu1 r s).trans ?_
    rw [map_mul, hc]
    exact (mul_le_of_le_one_left' hn1).trans (WithZero.exp_le_exp.2 (by omega)))
  have hgU : (z ^ n)⁻¹ * x.1 ∈ S.U := by
    refine Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ hz n)) x.2
  have hyU := ((S.U_eq _).1 hgU).1
  have hgram := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hPin l Z).2.2.2 i hi).1
  let z' : GlobalTheory.Mem.Col2.TC.GA B (B.R.N i) := z
  have hzmap : Matrix.GeneralLinearGroup.map (adAt B.host.F P.1) z' = Mu := Units.ext (Matrix.ext hzP)
  have key : Matrix.GeneralLinearGroup.map (adAt B.host.F P.1) ((z' ^ n)⁻¹ * x') = 1 := by
    rw [map_mul, map_inv, map_pow, hzmap, hMun, inv_mul_cancel]
  have hyP : ∀ r s, adAt B.host.F P.1 (((z ^ n)⁻¹ * x.1).1 r s) = (1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (P.1.adicCompletion B.fields.E)) r s :=
    fun r s => congrArg (fun g : GL (Fin (B.R.N i)) (P.1.adicCompletion B.fields.E) => g.1 r s) key
  have hover : ∀ w : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.E), w.under (𝓞 (I.rec7 l Z).host.F) = v → w = P.1 ∨ w = conjPrime₂ P.1 :=
    fun w hw => (GlobalTheory.Mem.Col2.under_eq_iff B.host P.1 w).1 (hw.trans hu.symm)
  have hyv : ∀ v', bc (prV (E := (I.rec7 l Z).host.E) v') ((z ^ n)⁻¹ * x.1) = 1 := by
    intro v'
    by_cases hv' : v' = v
    · rw [hv']
      exact bc_prV_eq_one_of_split (I.rec7 l Z).sp.cm hgram hyU P.1 v hover hyP
    · exact map_inv_pow_mul_eq_one _ n (hzv v' hv') (hxv v' hv')
  exact chi_eq_one_of_pow S.chi x ⟨z, hz⟩ n (hchi _) (S.chi_triv _ fun v' _ => hyv v')

end GlobalTheory.Mem.Col2.AdT.SplitChi

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelGroupPropertyClosedMul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevZeroInd

theorem redFn_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (PP : Pl E) {x y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (hx : x ∈ St β) (hy : y ∈ St β) : redFn β PP (x * y) = redFn β PP x * redFn β PP y := by
  unfold redFn ext1
  rw [dif_pos (mul_mem hx hy), dif_pos hx, dif_pos hy]
  rw [← map_mul]
  congr 1

theorem redFn_inv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (PP : Pl E) {x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (hx : x ∈ St β) : redFn β PP x⁻¹ = (redFn β PP x)⁻¹ := by
  unfold redFn ext1
  rw [dif_pos (inv_mem hx), dif_pos hx]
  rw [← map_inv]
  congr 1

theorem reductionBlock_injective_of_eq {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) (hn : n = r) :
    Function.Injective (upperLeftBlock (κ := κ) hr) := by
  subst hn
  intro a b h
  rwa [GlobalTheory.SeeConjRead.restrictedBlock_self_apply, GlobalTheory.SeeConjRead.restrictedBlock_self_apply] at h

theorem red_unique {D : D7} {u : D.what₂.Word} {d : GlobalTheory.SeeSaw.Dat D u}
    {τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E} {PP : Pl D.host.E}
    (G : GlobalTheory.LocMod.GAt d τ PP) {x : G.S.P.J} {g g' : GL (Fin D.R.r) (kP PP)} (h : G.Red x g) (h' : G.Red x g') :
    g = g' := by
  have h1 := G.hs
  let e : Fin D.R.k ⊕ Fin (G.s + 1) ≃ Fin D.R.r := finSumFinEquiv.trans (finCongr (by unfold Ranks.r; omega))
  have he : ∀ a, (e a).val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a := by
    rintro (a | a) <;> simp [e, GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos]
  refine Units.ext (Matrix.ext fun i j => ?_)
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (g.val (e i) (e j))
  obtain ⟨z', hz'⟩ := Ideal.Quotient.mk_surjective (g'.val (e i) (e j))
  have h2 := Valuation.map_sub_lt _ (h' i j _ _ (he i) (he j) z' hz') (h i j _ _ (he i) (he j) z hz)
  rw [sub_sub_sub_cancel_left] at h2
  rw [← hz, ← hz', Ideal.Quotient.eq, GlobalTheory.LocMod.SymChainAt.prO_lt G.q G.idem, map_sub]
  exact h2

end GlobalTheory.LevZeroInd

open GlobalTheory.LevZeroInd in
set_option maxHeartbeats 1000000 in

theorem GlobalTheory.LevZeroInd.gen : ∀ (D : D7) (u : D.what₂.Word) (d : GlobalTheory.SeeSaw.Dat D u) (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E) (G : ∀ PP : d.c.Pg, GlobalTheory.LocMod.GAt d τ PP.1) (cG : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m), d.Base → IsTypePlaces d.c.Pg → GlobalTheory.LocMod.PinGBy G cG → ∀ Q : GA D (d.st 0).V → Prop, (∀ k ∈ d.lev 0, ∀ k' ∈ d.lev 0, Q k → Q k' → Q (k * k')) → (∀ (PP : d.c.Pg) (n : GA D (d.st 0).V) (q : GL (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin ((G PP).s + 1)) (G PP).k), n ∈ flagN (d.bes 0 D.R.rS h0).d → q ∈ GlobalTheory.RootEx.N (G PP).k _ ((G PP).s + 1) (D.R.rS + 1) → (GlobalTheory.LocMod.ofSplit (G PP).q).IsLoc ((G PP).FY 0 ((G PP).s + 1) (Nat.zero_add _)) n q → (d.t 0)⁻¹ * n * d.t 0 ∈ d.lev 0 → Q ((d.t 0)⁻¹ * n * d.t 0)) → (∀ b ∈ GfC (D.sp.X 0), (d.t 0)⁻¹ * embA (d.bes 0 D.R.rS h0).d (d.bes 0 D.R.rS h0).o b * d.t 0 ∈ d.lev 0 → Q ((d.t 0)⁻¹ * embA (d.bes 0 D.R.rS h0).d (d.bes 0 D.R.rS h0).o b * d.t 0)) → (∀ k ∈ d.lev 0, (∀ PP ∈ d.c.Pg, redFn (d.st 0).β PP (finE (d.st 0).V k) = 1) → Q k) → ∀ k ∈ d.lev 0, Q k := by
  intro D u d τ G cG h0 hB hT hP Q hmul hN hU hred
  classical
  have hm : 0 < D.R.m := by omega
  have hst := hB.st 0 hm
  obtain ⟨hr, ξ, hL⟩ := hst.lev
  have hn : (d.st 0).V.rank = D.R.r := by rw [hst.rank]; show D.R.r + 0 * D.R.t = D.R.r; simp
  have key := fun x => GlobalTheory.LevYZero.lev_datY_zero _ (d.st 0).β _ D.R.r D.R.t hr hn d.c.Pg d.c.P d.c.chi ξ hL
    (Lev.finE (d.st 0).V x) (GlobalTheory.LevSplit.finE_mem_UA _ x)
  have hSt : ∀ x ∈ d.lev 0, Lev.finE (d.st 0).V x ∈ St (d.st 0).β := fun x hx => ((key x).1.1 hx.2).1
  have hRed : ∀ x ∈ d.lev 0, ∀ PP : d.c.Pg, ∃ z, (G PP).Red z (upperLeftBlock hr (redFn (d.st 0).β PP.1 (Lev.finE (d.st 0).V x))) :=
    fun x hx PP => (hP.grp _).1 ((key x).1.1 hx.2).2 PP
  have hmulm : ∀ x ∈ d.lev 0, ∀ y ∈ d.lev 0, x * y ∈ d.lev 0 := fun x hx y hy => by
    unfold GlobalTheory.SeeSaw.Dat.lev levS at *
    exact Subgroup.mul_mem _ hx hy
  have hinvm : ∀ x ∈ d.lev 0, x⁻¹ ∈ d.lev 0 := fun x hx => by
    unfold GlobalTheory.SeeSaw.Dat.lev levS at *
    exact Subgroup.inv_mem _ hx
  have claim : ∀ s : Finset (Pl D.host.E), ∀ k ∈ d.lev 0,
      (∀ PP ∈ d.c.Pg, PP ∉ s → redFn (d.st 0).β PP (Lev.finE (d.st 0).V k) = 1) → Q k := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro k hk h
      exact hred k hk fun PP hPP => h PP hPP (Finset.notMem_empty _)
    · intro a s ha ih k hk h
      by_cases haP : a ∈ d.c.Pg
      · obtain ⟨z, hz⟩ := hRed k hk ⟨a, haP⟩
        obtain ⟨m, hm0, hQm, hmr, hmo⟩ := GlobalTheory.T.level_group_property_closed_mul_alt D u d τ G cG h0 hB hT hP Q hmul hN hU ⟨a, haP⟩ z
        have e1 : redFn (d.st 0).β a (Lev.finE (d.st 0).V m) = redFn (d.st 0).β a (Lev.finE (d.st 0).V k) :=
          reductionBlock_injective_of_eq hr hn (red_unique (G ⟨a, haP⟩) (hmr hr) hz)
        have hk1 : m⁻¹ * k ∈ d.lev 0 := hmulm _ (hinvm m hm0) k hk
        have hred1 : ∀ PP, redFn (d.st 0).β PP (Lev.finE (d.st 0).V (m⁻¹ * k)) =
            (redFn (d.st 0).β PP (Lev.finE (d.st 0).V m))⁻¹ * redFn (d.st 0).β PP (Lev.finE (d.st 0).V k) := fun PP => by
          rw [map_mul, map_inv, redFn_mul _ _ (inv_mem (hSt m hm0)) (hSt k hk), redFn_inv _ _ (hSt m hm0)]
        have hQ1 := ih (m⁻¹ * k) hk1 fun PP hPP hPs => by
          rw [hred1]
          by_cases hPa : PP = a
          · subst hPa
            rw [e1, inv_mul_cancel]
          · rw [hmo PP hPP hPa, h PP hPP (by simp [hPa, hPs]), inv_one, one_mul]
        have := hmul m hm0 _ hk1 hQm hQ1
        simpa using this
      · exact ih k hk fun PP hPP hPs => h PP hPP (by
          simp only [Finset.mem_insert, not_or]
          exact ⟨fun e => haP (e ▸ hPP), hPs⟩)
  intro k hk
  exact claim d.c.Pg k hk fun PP hPP h => absurd hPP h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedVacuumAtIdentityNonzeroConstant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section
namespace GlobalTheory.AdForm.VacAllBase

theorem thetaSpace_std_line {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (i : ℕ) (hi : i + 1 ≤ B.R.m) : ∀ F ∈ Formalism.L2.Th1.H.Th (HV I.A.sc) (alV (I.rec7 l Z).host.d I.A.sc) (LamC (tauE (I.rec7 l Z)) I.A.δ ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N i)) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N (i + 1)))), ∃ c : ℂ, F = c • I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N i)) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N (i + 1))) := by
  intro F hF
  let Bk : Formalism.L2.Ker.Base (I.rec7 l Z) ⊤ I.J.δ := GlobalTheory.Mem.Col2.Th.VacIn.toRec (D := I.rec7 l Z) I.J.V
  have hS : Bk.StdOK := GlobalTheory.FourthRootStd.stdOK Bk (GlobalTheory.Glob.IntegralWittCoefficients.isCurveIdeal_top _)
    ((GlobalTheory.Mem.Col2.Th.isDiscriminantTwelfthRoot_host_iff (I.rec7 l Z) ⊤ I.J.δ).1 hI.amb_ok.delta)
  have hLa : LamC (tauE (I.rec7 l Z)) I.A.δ ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N i)) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N (i + 1))) = Formalism.MainNotions.TaylorLogMetric.La (I.rec7 l Z) (Formalism.MainNotions.TaylorLogMetric.tor0 (I.rec7 l Z) ⊤ I.J.δ) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N i)) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N (i + 1))) := by
    rw [← Formalism.L2.KerInert.RepComb.lamK_eq, Formalism.L2.KerInert.RepComb.lamK, GlobalTheory.ThetaLineStd.aaOf_top]
    rfl
  have hH : (HV (ι := (I.rec7 l Z).what₂.Tau) (a := B.R.N i) (b := B.R.N (i + 1)) I.A.sc) = formV (Formalism.MainNotions.TaylorLogMetric.area (Formalism.MainNotions.TaylorLogMetric.lamOf (I.rec7 l Z) ⊤ I.J.δ)) (I.rec7 l Z).what₂.Tau (B.R.N i) (B.R.N (i + 1)) :=
    Formalism.L2.KerInert.RepComb.HV_eq_formV _
  rw [hLa, alV, hH] at hF
  have hF' : F ∈ Formalism.L2.Th1.H.Th (formV (Formalism.MainNotions.TaylorLogMetric.area (Formalism.MainNotions.TaylorLogMetric.lamOf (I.rec7 l Z) ⊤ I.J.δ)) (I.rec7 l Z).what₂.Tau (B.R.N i) (B.R.N (i + 1))) (Formalism.MainNotions.TaylorLogMetric.al (I.rec7 l Z) Bk.tor) (Formalism.MainNotions.TaylorLogMetric.La (I.rec7 l Z) Bk.tor (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N i)) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N (i + 1)))) := by
    refine Formalism.L2.Ker.Th_congr _ _ _ _ (fun x hx => ?_) hF
    obtain ⟨m, hm⟩ := Bk.qInt0 hS _ _ x hx
    exact (Formalism.L2.Ker.al_eq _ Bk.tor x m hm).symm
  obtain ⟨c, hc⟩ := Formalism.L2.PairingIndexBounds.Eq.J.thZeroSpans hS _ _ F hF'
  refine ⟨c, ?_⟩
  have hM : I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N i)) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N (i + 1))) = Bk.thMoved (B.R.N i) (B.R.N (i + 1)) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N i)) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N (i + 1))) := rfl
  obtain ⟨x, hx, hIx⟩ := GlobalTheory.NatAtStd.Iop_self (I.rec7 l Z) Bk.tor (Formalism.MainNotions.TaylorLogMetric.La (I.rec7 l Z) Bk.tor (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N i)) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N (i + 1))))
  have hfix : (fun z => Formalism.MainNotions.TaylorLogMetric.al (I.rec7 l Z) Bk.tor x * Formalism.MainNotions.TaylorLogMetric.U (I.rec7 l Z) Bk.tor x (Bk.thZero (B.R.N i) (B.R.N (i + 1))) z) = Bk.thZero (B.R.N i) (B.R.N (i + 1)) :=
    funext fun z => (Bk.thZeroMem hS _ _).2 x hx z
  have hMz : Bk.thMoved (B.R.N i) (B.R.N (i + 1)) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N i)) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N (i + 1))) = Bk.thZero (B.R.N i) (B.R.N (i + 1)) := by
    unfold Formalism.L2.Ker.Base.thMoved Formalism.L2.Ker.Base.thHalf
    rw [hIx, hIx, hfix, hfix]
  rw [hM, hMz]
  exact hc

theorem moveT_one : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) ψ θ, IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) vac, IsVacO ψ θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) (fun _ => 1) (fun _ => 1) (intVec _ _) (intVec _ _) vac → ∀ (a : I.ι) μ om, ChrEq μ (I.C.mu0 ⟨i, hi⟩ * I.xi a) → IsWeilDatumO ψ _ _ μ μ om → ∃ c₀ : ℂ, c₀ ≠ 0 ∧ GlobalTheory.AdForm.VacAll.MoveT I l Z θ i hi c₀ μ om vac 1 1 := by
  intro B X I hI hP l Z ψ θ hψ hθ i hi vac hvac a μ om _ hom
  have hstd := (GlobalTheory.AdForm.StdStepsT.stdPair_steps_all I hI hP l Z ψ θ hψ hθ).1 i hi
  have key := GlobalTheory.T.movedWeilVacuum_eq_vacuum_of_movedLattices (I.rec7 l Z) ψ θ _ _ _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi)
    I.A.δ I.A.sc hstd μ om hom vac hvac 1 (one_mem _) 1 (one_mem _)
  have S1 : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n) (N : Submodule (𝓞 D.host.E) (Fin n → D.host.E)),
      Moves V hn 1 N → N = Formalism.L2.Col.stdLat D.host.E n := GlobalTheory.T.adelicTranslate_one_eq_standardLattice
  have S2 : ∀ (D : D7) (μ : (AE D)ˣ →* Circle) (n : ℕ), ResEta D μ n → Even n → ∀ (V : HSp D) (x : (AE D)ˣ),
      IsDetRoot V 1 x → μ x = 1 := GlobalTheory.T.character_eq_one_of_isDetRoot_of_even
  have S3 := thetaSpace_std_line I hI l Z i hi
  by_cases hex : Moves _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) 1 (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N i)) ∧
      Moves _ (rankN (I.rec7 l Z) (i + 1) hi) 1 (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N (i + 1)))
  · obtain ⟨-, hmem, hne⟩ := key _ _ hex.1 hex.2
    obtain ⟨c, hc⟩ := S3 _ hmem
    refine ⟨c, ?_, ?_⟩
    · rintro rfl
      apply hne
      exact hc.trans (zero_smul _ _)
    · intro N N' hN hN' x y hx hy
      obtain rfl := S1 _ _ _ _ N hN
      obtain rfl := S1 _ _ _ _ N' hN'
      have hx1 : μ x = 1 := S2 _ _ _ hom.resS hstd.rk.2.2.1 _ x hx
      have hy1 : μ y = 1 := S2 _ _ _ hom.resT hstd.rk.2.2.2 _ y hy
      rw [hx1, hy1]
      show xiN θ _ _ _ _ I.A.δ I.A.sc _ = _
      refine hc.trans ?_
      funext z
      simp only [Pi.smul_apply, smul_eq_mul, Circle.coe_one, inv_one, mul_one]
      rfl
  · refine ⟨1, one_ne_zero, ?_⟩
    intro N N' hN hN'
    exact absurd ⟨S1 _ _ _ _ N hN ▸ hN, S1 _ _ _ _ N' hN' ▸ hN'⟩ hex

end GlobalTheory.AdForm.VacAllBase
end
end

