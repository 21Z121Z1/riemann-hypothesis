import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0512
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0527
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0542
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0551
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0233
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasLocalSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1695
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0091
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0556
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0217
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0523
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0404
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0304
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0558
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0552
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0553
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0534

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ActOChiRight
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section

open GlobalTheory.StdFrames
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
namespace GlobalTheory.RowMoveAt
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem notOff (S : GridChoice W U) {t : T} (ht : t ∈ U) {w : Pl D.host.E} (hw : w ∈ locPl G t) : ¬ Off S.N.S w := by
  classical
  intro h0
  have h3 := S.N.off w h0
  rcases Finset.mem_union.1 hw with h | h
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
    exact h3.1 (by rw [G.pl.under_w hv]; exact hv)
  · exact h3.2.1 t ht w h rfl

theorem cpt_supp_zero {S : Finset ℕ} {w : Pl D.host.E} (hw : ¬ Off S w) {P : Finset (Pl D.host.E)} {e : AE D}
    (he : IsIdemSum e P) (hoff : ∀ w' ∈ P, Off S w') : cpt w (toEAf D (e + cA D e)) = 0 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  rw [map_sum, ← Finset.sum_add_distrib, map_sum, map_sum]
  refine Finset.sum_eq_zero fun w' hw' => ?_
  obtain ⟨hne, hnc⟩ := GlobalTheory.StdHalfLat.ne_and_not_conj hw (hoff w' hw')
  rw [map_add, map_add, (cpt_of_isIdemAt (hes w' hw')).2 w hne,
    (cpt_of_isIdemAt (GlobalTheory.MovedIdem.isIdemAt_conj (hes w' hw') (GlobalTheory.IdemSupport.mem_cP w'))).2 w ?_, add_zero]
  rintro rfl
  apply hnc
  intro c hc
  exact ⟨GlobalTheory.IdemSupport.cO D c, (GlobalTheory.IdemSupport.mem_cP w' c).1 hc, by simp [GlobalTheory.IdemSupport.cO]⟩

theorem map_mt_eq_one {S : Finset ℕ} {w : Pl D.host.E} (hw : ¬ Off S w) {P : Finset (Pl D.host.E)} {e : AE D}
    (he : IsIdemSum e P) (hoff : ∀ w' ∈ P, Off S w') {V : HSp D} {g : GA D V} (hg : SuppAt e V g) :
    (mt V g).map ((cpt w).comp (toEAf D)) = 1 := by
  have h0 := cpt_supp_zero hw he hoff
  have h1 : (mt V g - 1).map ((cpt w).comp (toEAf D)) = 0 := by
    ext i j
    rw [Matrix.map_apply, ← hg i j, RingHom.comp_apply, map_mul, map_mul, h0, zero_mul, Matrix.zero_apply]
  have h2 : (mt V g).map ((cpt w).comp (toEAf D)) =
      (mt V g - 1).map ((cpt w).comp (toEAf D)) + (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).map ((cpt w).comp (toEAf D)) := by
    rw [← Matrix.map_add _ (map_add _), sub_add_cancel]
  rw [h2, h1, zero_add, Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.RowMoveAt

namespace GlobalTheory.RowMoveAt
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem actO_chi_right (j : ℕ) (M : GA D (G.V (.grid (j + 1) D.R.m)))
    (x : WO (G.pS (.chi j D.R.m : Pair T)) (G.pT (.chi j D.R.m : Pair T))) :
    actO _ _ (G.toPair (.chi j D.R.m) 1 M)⁻¹.1 (G.toPair (.chi j D.R.m) 1 M)⁻¹.2 x =
      (x : Matrix _ _ (AE D)) * mt (G.V (.grid (j + 1) D.R.m)) M := by
  simp only [actO, GridData.toPair, Prod.fst_inv, Prod.snd_inv, inv_inv, inv_one]
  rw [show mt (G.pT (.chi j D.R.m : Pair T)) 1 = 1 from rfl, Matrix.one_mul]
  rfl

theorem actO_chi_left (j : ℕ) (M : GA D (G.V (.grid (j + 1) D.R.m)))
    (x : WO (G.pS (.chi (j + 1) D.R.m : Pair T)) (G.pT (.chi (j + 1) D.R.m : Pair T))) :
    actO _ _ (G.toPair (.chi (j + 1) D.R.m) M 1)⁻¹.1 (G.toPair (.chi (j + 1) D.R.m) M 1)⁻¹.2 x =
      mt (G.V (.grid (j + 1) D.R.m)) M⁻¹ * (x : Matrix _ _ (AE D)) := by
  simp only [actO, GridData.toPair, Prod.fst_inv, Prod.snd_inv, inv_inv, map_one, inv_one]
  rw [show mt (G.pS (.chi (j + 1) D.R.m : Pair T)) 1 = 1 from rfl, Matrix.mul_one]

theorem sub_mul_cast {K : Type} [Field K] {a b a' b' : ℕ} (ha : a' = a) (hb : b' = b) (P : GL (Fin a) K) (Q : GL (Fin b) K)
    (Y : Matrix (Fin a) (Fin b) K) (X : Matrix (Fin b) (Fin b) K) :
    ((P⁻¹).val * (Y * X) * Q.val).submatrix (Fin.cast ha) (Fin.cast hb) =
      ((P⁻¹).val * Y * Q.val).submatrix (Fin.cast ha) (Fin.cast hb) * ((Q⁻¹).val * X * Q.val).submatrix (Fin.cast hb) (Fin.cast hb) := by
  rw [← Matrix.submatrix_mul _ _ (Fin.cast ha) (Fin.cast hb) (Fin.cast hb) (finCongr hb).bijective]
  congr 1
  simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left]

theorem mul_sub_cast {K : Type} [Field K] {a b a' b' : ℕ} (ha : a' = a) (hb : b' = b) (P : GL (Fin a) K) (Q : GL (Fin b) K)
    (Y : Matrix (Fin a) (Fin b) K) (X : Matrix (Fin a) (Fin a) K) :
    ((P⁻¹).val * (X * Y) * Q.val).submatrix (Fin.cast ha) (Fin.cast hb) =
      ((P⁻¹).val * X * P.val).submatrix (Fin.cast ha) (Fin.cast ha) * ((P⁻¹).val * Y * Q.val).submatrix (Fin.cast ha) (Fin.cast hb) := by
  rw [← Matrix.submatrix_mul _ _ (Fin.cast ha) (Fin.cast ha) (Fin.cast hb) (finCongr ha).bijective]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (P.val), Units.mul_inv, Matrix.one_mul]

theorem inBasis_val {n n' : ℕ} (h : n' = n) (β x : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E) :
    (inBasis h β w x).val = (((loc w β)⁻¹).val * (loc w x).val * (loc w β).val).submatrix (Fin.cast h) (Fin.cast h) := by
  ext i j
  rw [GlobalTheory.FunObj.ProdOpen.inBasis_apply, ← map_inv, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul]
  rfl

end GlobalTheory.RowMoveAt

namespace GlobalTheory.RowMoveAt

theorem rowAt_move : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T}, t ∈ U → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)) (w : Pl D.host.E), w ∈ locPl G t →
    ∀ (y : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
    S.rowAt t w (Function.update (Function.update y ⟨j, by omega⟩
        (actO _ _ (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.1 (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.2
          (y ⟨j, by omega⟩) : WO (G.pS (.chi j D.R.m : Pair T)) (G.pT (.chi j D.R.m : Pair T))))
      ⟨j + 1, hj⟩ (actO _ _ (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.1
          (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.2 (y ⟨j + 1, hj⟩) :
          WO (G.pS (.chi (j + 1) D.R.m : Pair T)) (G.pT (.chi (j + 1) D.R.m : Pair T)))) =
    Function.update (Function.update (S.rowAt t w y) j
        (S.rowAt t w y j * @id (Matrix (Fin ((locGrid G t w).rank (j + 1, (locGrid G t w).m)))
            (Fin ((locGrid G t w).rank (j + 1, (locGrid G t w).m))) (Kw w)) (inBasis (rank_vertex G t w (X := (j + 1, D.R.m)) ⟨hj.le, le_rfl⟩) (S.B.β (j + 1) D.R.m) w
          (finG (G.V (.grid (j + 1) D.R.m)) k)).val))
      (j + 1) (@id (Matrix (Fin ((locGrid G t w).rank (j + 1, (locGrid G t w).m)))
            (Fin ((locGrid G t w).rank (j + 1, (locGrid G t w).m))) (Kw w)) (inBasis (rank_vertex G t w (X := (j + 1, D.R.m)) ⟨hj.le, le_rfl⟩) (S.B.β (j + 1) D.R.m) w
          (finG (G.V (.grid (j + 1) D.R.m)) k))⁻¹.val * S.rowAt t w y (j + 1)) := by
  intro D T L sc G W U S t ht j hj k w hw y
  have hX : DefNode D.R.m (.grid (j + 1) D.R.m) := ⟨by omega, rfl⟩
  obtain ⟨P, e, he, hsupp, hoff⟩ := S.N.u_supp _ hX
  have hn := notOff S ht hw
  have hu := map_mt_eq_one hn he hoff hsupp
  have hu' := map_mt_eq_one hn he hoff (GlobalTheory.StdHalfLat.suppAt_inv' hsupp)
  have hM : (mt _ (moved S j k)).map ((cpt w).comp (toEAf D)) = (loc w (finG (G.V (.grid (j + 1) D.R.m)) k)).val := by
    rw [show mt _ (moved S j k) = mt _ (S.N.u (.grid (j + 1) D.R.m)).1⁻¹ * mt _ k.1 * mt _ (S.N.u (.grid (j + 1) D.R.m)).1 from rfl,
      Matrix.map_mul, Matrix.map_mul, hu, hu', Matrix.one_mul, Matrix.mul_one]
    rfl
  have hM' : (mt _ (moved S j k)⁻¹).map ((cpt w).comp (toEAf D)) = (loc w (finG (G.V (.grid (j + 1) D.R.m)) k⁻¹)).val := by
    rw [show mt _ (moved S j k)⁻¹ = mt _ (S.N.u (.grid (j + 1) D.R.m)).1⁻¹ * mt _ k.1⁻¹ * mt _ (S.N.u (.grid (j + 1) D.R.m)).1 from by
      rw [RowVertexInv.moved]; simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv, mul_assoc]; rfl,
      Matrix.map_mul, Matrix.map_mul, hu, hu', Matrix.one_mul, Matrix.mul_one]
    rfl
  funext i

  by_cases h1 : i = j + 1
  · subst h1
    rw [Function.update_self]
    simp only [GridChoice.rowAt, dif_pos hj, Function.update_self, Frames.coord]
    rw [actO_chi_left, Matrix.map_mul, hM']
    erw [Matrix.transpose_transpose, Matrix.transpose_transpose, id_eq]
    rw [← map_inv (inBasis _ (S.B.β (j + 1) D.R.m) w), map_inv (finG (G.V (Node.grid (j + 1) D.R.m))) k, inBasis_val, mul_sub_cast]
    rfl
  by_cases h2 : i = j
  · subst h2
    rw [Function.update_of_ne (by omega), Function.update_self]
    have hj' : i < D.R.m := by omega
    simp only [GridChoice.rowAt, dif_pos hj', Frames.coord]
    rw [Function.update_of_ne (fun h => by simp [Fin.ext_iff] at h), Function.update_self, actO_chi_right, Matrix.map_mul, hM]
    erw [Matrix.transpose_transpose, Matrix.transpose_transpose, id_eq]
    rw [inBasis_val, sub_mul_cast]
    rfl
  · rw [Function.update_of_ne h1, Function.update_of_ne h2]
    simp only [GridChoice.rowAt]
    by_cases hi : i < D.R.m
    · rw [dif_pos hi, dif_pos hi, Function.update_of_ne (fun h => h1 (by simpa [Fin.ext_iff] using h)),
        Function.update_of_ne (fun h => h2 (by simpa [Fin.ext_iff] using h))]
    · rw [dif_neg hi, dif_neg hi]
end GlobalTheory.RowMoveAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AutomorphicTypeFiniteDimStable
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.FiniteGKSum

open GlobalTheory.SeriesToClosure Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.PointAtPlaceHom GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes
open Matrix Filter
open scoped InnerProductSpace Topology

section Sums

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (τ : D.what₂.Tau)
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin V.rank → Bool)
  (σ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (H →L[ℂ] H)) (P : Matrix (Fin V.rank) (Fin V.rank) ℂ)

def gkSums : Submodule ℂ (GA D V → ℂ) where
  carrier := {ψ | ∃ (m : ℕ) (T : Fin m → (kFin ε σ →ₗ[ℂ] (GA D V → ℂ))) (p : Fin m → kFin ε σ),
    (∀ j, IsGKMap θ V τ ε σ P (T j)) ∧ ψ = ∑ j, T j (p j)}
  zero_mem' := ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨m, T, p, hT, rfl⟩ ⟨m', T', p', hT', rfl⟩
    refine ⟨m + m', Fin.append T T', Fin.append p p', fun j => ?_, ?_⟩
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simpa using hT j
      · simpa using hT' j
    · simp [Fin.sum_univ_add]
  smul_mem' := by
    rintro c _ ⟨m, T, p, hT, rfl⟩
    exact ⟨m, T, fun j => c • p j, hT, by simp [Finset.smul_sum]⟩

end Sums

section Closure

variable {D : D7} {V : HSp D}

theorem mem_of_approx {E : Submodule ℂ (GA D V → ℂ)} [FiniteDimensional ℂ E] {φ : GA D V → ℂ}
    (h : ∀ C : Set (GA D V), IsCompact C → ∀ δ : ℝ, 0 < δ → ∃ ψ ∈ E, ∀ x ∈ C, ‖φ x - ψ x‖ < δ) : φ ∈ E := by
  have hE : IsClosed (E : Set (GA D V → ℂ)) := Submodule.closed_of_finiteDimensional E
  have key : ∀ p : Finset (GA D V) × ℕ, ∃ ψ ∈ E, ∀ x ∈ p.1, ‖φ x - ψ x‖ < 1 / ((p.2 : ℝ) + 1) :=
    fun p => h _ p.1.finite_toSet.isCompact _ (by positivity)
  choose u hu hu' using key
  refine hE.mem_of_tendsto (f := u) (b := (atTop : Filter (Finset (GA D V) × ℕ))) ?_
    (Filter.Eventually.of_forall hu)
  refine tendsto_pi_nhds.2 fun x => Metric.tendsto_atTop.2 fun δ hδ => ?_
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  refine ⟨({x}, N), fun p hp => ?_⟩
  have h1 : x ∈ p.1 := hp.1 (Finset.mem_singleton_self x)
  have h2 : (N : ℝ) ≤ p.2 := by exact_mod_cast hp.2
  rw [dist_comm, dist_eq_norm]
  calc ‖φ x - u p x‖ < 1 / ((p.2 : ℝ) + 1) := hu' p x h1
    _ ≤ 1 / ((N : ℝ) + 1) := by gcongr
    _ < δ := hN

end Closure

section Avg

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {τ : D.what₂.Tau}
  {ε : Fin V.rank → Bool} {P : Matrix (Fin V.rank) (Fin V.rank) ℂ}

theorem avg_mem (hθ : IsInfFam (D := D) θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ)
    {W : Submodule ℂ (GA D V → ℂ)} [FiniteDimensional ℂ W]
    (hW : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), P * g * P⁻¹ ∈ Formalism.REAL.Kset ε →
      ∀ h ∈ W, rTr V (atTau θ V τ g) h ∈ W)
    {φ : GA D V → ℂ} (hφc : Continuous φ) (hφ : φ ∈ W) {e : KG ε → ℂ} (he : KFinFun ε e) :
    avg θ V τ ε P e φ ∈ W := by
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hk : Continuous fun k : KG ε => atTau θ V τ (P⁻¹ * toMK k * P) :=
    (continuousOn_atTau hθ V τ).comp_continuous continuous_conjK
      fun k => conj_inv_mem hP hJ (K_le_UJ (toMK_mem_K k))
  have hd := (isUnit_iff_isUnit_det _).1 hP
  have cc : ∀ g : Matrix (Fin V.rank) (Fin V.rank) ℂ, P * (P⁻¹ * g * P) * P⁻¹ = g := fun g => by
    calc P * (P⁻¹ * g * P) * P⁻¹ = (P * P⁻¹) * g * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [Matrix.mul_nonsing_inv _ hd]; simp
  have hmem : ∀ k : KG ε, rTr V (atTau θ V τ (P⁻¹ * toMK k * P)) φ ∈ W := fun k =>
    hW _ (conj_inv_mem hP hJ (K_le_UJ (toMK_mem_K k))) (by rw [cc]; exact toMK_mem_K k) φ hφ
  let f : KG ε → W := fun k => ⟨_, hmem k⟩
  have hf : Continuous f := (continuous_pi fun x => hφc.comp (continuous_const.mul hk)).subtype_mk _
  let b := Module.finBasis ℂ W
  have hc : ∀ i, Continuous fun k => b.coord i (f k) := fun i =>
    (LinearMap.continuous_of_finiteDimensional (b.coord i)).comp hf
  have he' : Continuous e := by obtain ⟨F, -, h1, h2, -⟩ := he; exact h2 _ h1
  have hint : ∀ i, Integrable (fun k => e k * b.coord i (f k)) (muK ε) := fun i =>
    integrableOn_univ.mp ((he'.mul (hc i)).continuousOn.integrableOn_compact isCompact_univ)
  have hrep : ∀ k, (f k : GA D V → ℂ) = ∑ i, b.coord i (f k) • (b i : GA D V → ℂ) := fun k => by
    nth_rw 1 [← b.sum_repr (f k)]
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    rfl
  have key : avg θ V τ ε P e φ = ∑ i, (∫ k, e k * b.coord i (f k) ∂(muK ε)) • (b i : GA D V → ℂ) := by
    funext x
    have hx : ∀ k, φ (x * atTau θ V τ (P⁻¹ * toMK k * P)) = ∑ i, b.coord i (f k) * (b i : GA D V → ℂ) x :=
      fun k => by
        have := congrFun (hrep k) x
        simpa [f, rTr, Finset.sum_apply] using this
    simp only [avg, hx, Finset.mul_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [integral_finset_sum _ fun i _ => ?_]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [← integral_mul_const]
      congr 1
      funext k
      ring
    · simpa [mul_assoc] using (hint i).mul_const ((b i : GA D V → ℂ) x)
  rw [key]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (b i).2

end Avg

end GlobalTheory.FiniteGKSum

namespace GlobalTheory.FiniteGKSum
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.PointAtPlaceHom GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes GlobalTheory.SeriesToClosure
  GlobalTheory.FiniteGKSum in

theorem finite_sum_of_gkMaps : GlobalTheory.FunPr.Hypotheses₂ → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (V : HSp D) (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ (τ : D.what₂.Tau) (φ : GA D V → ℂ), IsAutFunSm θ V φ → IsTypeAt θ V τ (S τ) φ →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ φ ∈ W ∧ ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) → ∀ h ∈ W, rTr V (atTau θ V τ g) h ∈ W) →
    ∃ (m : ℕ) (T : Fin m → (GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) →ₗ[ℂ] (GA D V → ℂ)))
      (p : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
      (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.IsGKMap θ V τ (M.ε τ) (M.σ τ) (M.fr τ) (T j)) ∧ φ = ∑ j, T j (p j) := by
  intro hPr D θ V S M hθ τ φ hφ hT ⟨W, hWf, hφW, hWK⟩
  haveI := hWf
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  obtain ⟨H', i1, i2, σ', lam', ε', P', hE', hD', hP', hJ', hx⟩ := hT
  obtain ⟨rfl, rfl⟩ := GlobalTheory.SignedParTest.isEnum_unique (M.enum τ) hE'
  obtain ⟨U, hU⟩ := hPr.discreteSeriesHermitianUnique _ (M.ε τ) (M.lam τ)
    (GlobalTheory.Published.HermitianUnique.isHCParam_of_isDS (M.enum τ).1 (M.ds τ)) _ (M.fr τ) P' (M.fr_unit τ) hP'
    (M.fr_gram τ) hJ' _ _ (M.σ τ) σ' (M.ds τ) hD'
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  have hσ : Std (M.ε τ) (M.σ τ) := std_of_isDS hPr.harishChandraModules (M.ds τ)
  have hP := M.fr_unit τ
  have hJ := M.fr_gram τ
  have hx' : ∀ x, HasTypeAll (lieSet (M.ε τ)) (UJset (M.ε τ)) (M.σ τ) (res θ V τ (M.fr τ) φ x) := fun x =>
    hasTypeAll_transport _ H' (M.H τ) _ (M.σ τ) (gramAt D V τ) (Jm (M.ε τ)) (M.fr τ) (isUnit_gram hP' hJ') hP hJ U
      hU (fun g => φ (x * atTau θ V τ g)) (hasTypeAll_iff.2 (hx x))
  choose Sx hS hc v ℓ C h using hx'
  have hZ : ∀ e, KFinFun (M.ε τ) e →
      avg θ V τ (M.ε τ) (M.fr τ) e φ ∈ gkSums θ V τ (M.ε τ) (M.σ τ) (M.fr τ) := by
    intro e he
    obtain ⟨m, a, c, ha, hQ, hA⟩ := exists_rank_one hθ hP hJ hσ he
    choose T hT hTv using fun j => exists_gkMap hθ hP hJ hσ hφ hS hc h (hA j)
    refine ⟨m, T, fun j => ⟨a j, mem_kFin_iff.2 (ha j)⟩, hT, funext fun x => ?_⟩
    have h1 := (moves_avg hθ hP hJ hσ he φ x _ _ _ _ (hS x) (hc x) (h x)).1.2.2.2.2 1 (one_mem_UJ _)
    simp only [res_one hθ hP, sigma_one hσ.1, hQ, map_sum, map_smul, smul_eq_mul] at h1
    have h2 := h1.unique (hasSum_sum fun j _ => (Expn.summable_term (h x) (c j) (hσ.2.2.1 _ (ha j))).hasSum)
    simp only [Finset.sum_apply, hTv]
    exact h2
  have hk : Continuous fun k : KG (M.ε τ) => atTau θ V τ ((M.fr τ)⁻¹ * toMK k * M.fr τ) :=
    (continuousOn_atTau hθ V τ).comp_continuous continuous_conjK
      fun k => conj_inv_mem hP hJ (K_le_UJ (toMK_mem_K k))
  have hmem : φ ∈ gkSums θ V τ (M.ε τ) (M.σ τ) (M.fr τ) ⊓ W := by
    haveI : FiniteDimensional ℂ (gkSums θ V τ (M.ε τ) (M.σ τ) (M.fr τ) ⊓ W : Submodule ℂ _) :=
      Submodule.finiteDimensional_of_le inf_le_right
    refine mem_of_approx fun K hK δ hδ => ?_
    obtain ⟨e, he, hap⟩ := GlobalTheory.T.exists_compactFinite_approxIdentity _ (M.ε τ) (GA D V)
      (fun x k => φ (x * atTau θ V τ ((M.fr τ)⁻¹ * toMK k * M.fr τ)))
      (hφ.cont.comp (continuous_fst.mul (hk.comp continuous_snd))) K hK δ hδ
    refine ⟨avg θ V τ (M.ε τ) (M.fr τ) e φ, ⟨hZ e he, avg_mem hθ hP hJ hWK hφ.cont hφW he⟩, fun x hxK => ?_⟩
    have h4 : φ (x * atTau θ V τ ((M.fr τ)⁻¹ * toMK (1 : KG (M.ε τ)) * M.fr τ)) = φ x := res_one hθ hP φ x
    have h3 := hap x hxK
    rw [h4] at h3
    exact h3
  obtain ⟨m, T, p, hT, hsum⟩ := hmem.1
  exact ⟨m, T, p, hT, hsum⟩

end GlobalTheory.FiniteGKSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AveragePreservesKFinitenessStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.average_preserves_K_finiteness : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (ψ : GA D N.V → ℂ), IsAutFunSm θ N.V ψ → ∀ (τ τ' : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ') → ℂ), GlobalTheory.TypeSum.KFinFun (N.M.ε τ') e → GlobalTheory.CuspKFin.KFinAt θ N τ ψ → GlobalTheory.CuspKFin.KFinAt θ N τ (GlobalTheory.SeriesToClosure.avg θ N.V τ' (N.M.ε τ') (N.M.fr τ') e ψ) := by
  first | exact @GlobalTheory.CuspKFin.kFinAt_avg_of_kFinAt | exact GlobalTheory.CuspKFin.kFinAt_avg_of_kFinAt | (intros; apply GlobalTheory.CuspKFin.kFinAt_avg_of_kFinAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AveragedAutomorphicFunctionKFinite
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size

noncomputable section

namespace GlobalTheory.CuspKFinAvg

open Formalism.REAL Matrix

def leftReg {K : Type} [Group K] (F : Submodule ℂ (K → ℂ)) (hF : ∀ φ ∈ F, ∀ k₀ : K, (fun k => φ (k₀ * k)) ∈ F) :
    Representation ℂ K F where
  toFun k :=
    { toFun := fun f => ⟨fun y => (f : K → ℂ) (k⁻¹ * y), hF _ f.2 k⁻¹⟩
      map_add' := fun f g => rfl
      map_smul' := fun c f => rfl }
  map_one' := by
    ext f y
    simp
  map_mul' := fun a b => by
    ext f y
    simp [mul_assoc]

end GlobalTheory.CuspKFinAvg

namespace GlobalTheory.CuspKFin

open Formalism.REAL Matrix MeasureTheory

theorem kFinAt_avg : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (ψ : GA D N.V → ℂ),
    IsAutFunSm θ N.V ψ → ∀ (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e →
    GlobalTheory.CuspKFin.KFinAt θ N τ (GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e ψ) := by
  first
  | exact @_root_.GlobalTheory.LeftRegularRepresentation.kFinAt_avg
  | exact _root_.GlobalTheory.LeftRegularRepresentation.kFinAt_avg
  | (apply _root_.GlobalTheory.LeftRegularRepresentation.kFinAt_avg <;> assumption)
  | (intros; apply _root_.GlobalTheory.LeftRegularRepresentation.kFinAt_avg <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LeftRegularRepresentation.kFinAt_avg <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LeftRegularRepresentation.kFinAt_avg ..)

end GlobalTheory.CuspKFin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomTriangleFiniteDoubleCosetsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottom_triangle_finite_double_cosets : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∀ J : Subgroup (GA D WW), IsOpen (J : Set (GA D WW)) → ∃ H : Finset (GA D WW), (∀ h ∈ H, h ∈ GfC WW) ∧
      ∀ h ∈ GfC WW, ∃ γ ∈ GQ WW, ∃ r ∈ GinfC WW, ∃ h₀ ∈ H, ∃ κ ∈ J, κ ∈ GfC WW ∧ h = γ * r * h₀ * κ := by
  first | exact @GlobalTheory.BotClassFin.exists_reps | exact GlobalTheory.BotClassFin.exists_reps | (intros; apply GlobalTheory.BotClassFin.exists_reps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjFockPureTensorMapNegFormSpaceEqStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Chain.RealIt GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_fockPureTensorMap_negFormSpace_eq : ∀ {D : D7} (S T : GlobalTheory.Grid.Node D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (f : WO S.V T.V → ℂ), IsStdChar D ψ (-1) → IsInfFam θ → IsThetaFunO ψ (GlobalTheory.Grid.neg S.V) T.V f → ∀ P : GlobalTheory.Grid.Pol S T, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (GlobalTheory.Grid.fock ψ θ true S T f P) = GlobalTheory.Chain.ptOf ψ θ S.M T.M (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) (MvPolynomial.map (starRingEnd ℂ) P) := by
  first | exact @GlobalTheory.FockConjNeg.fock_neg_cj | exact GlobalTheory.FockConjNeg.fock_neg_cj | (intros; apply GlobalTheory.FockConjNeg.fock_neg_cj <;> assumption)
end

