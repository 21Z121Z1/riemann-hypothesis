import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0063
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0082
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0004
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.GaussJetBounds.Bundle0004
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DerivationCoordinateChange
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0008
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0428
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0437
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0129
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementE
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0083

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankDpstUnramifiedLeDimRepresentation
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.Pst GlobalTheory.WeilDeligne TensorProduct Module

noncomputable section

namespace GlobalTheory.PstRank

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
  (ρ : Representation LL ↥(GK K) V)

def sigSt (g : ↥(GK K)) : Bst P ⊗[ℚ_[l]] V →ₗ[ℚ_[l]] Bst P ⊗[ℚ_[l]] V :=
  TensorProduct.map (actSt P (g : GQ l)).toLinearMap ((ρ g).restrictScalars ℚ_[l])

theorem sigSt_smul (g : ↥(GK K)) (b : Bst P) (w : Bst P ⊗[ℚ_[l]] V) :
    sigSt P ρ g (b • w) = actSt P (g : GQ l) b • sigSt P ρ g w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul c v => simp [sigSt, TensorProduct.smul_tmul']
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

theorem sigSt_comm (g : ↥(GK K)) (y : V ⊗[ℚ_[l]] Bst P) :
    sigSt P ρ g (TensorProduct.comm ℚ_[l] V (Bst P) y) =
      TensorProduct.comm ℚ_[l] V (Bst P) (stRep P ρ g y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [sigSt]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem comm_mulV (c : ↥(MaximalUnramifiedExtension l)) (y : V ⊗[ℚ_[l]] Bst P) :
    TensorProduct.comm ℚ_[l] V (Bst P) (mulV P LL V c y) = c • TensorProduct.comm ℚ_[l] V (Bst P) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [TensorProduct.smul_tmul', Algebra.smul_def]
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

def toB : DpstUr P ρ →ₗ[↥(MaximalUnramifiedExtension l)] Bst P ⊗[ℚ_[l]] V where
  toFun x := TensorProduct.comm ℚ_[l] V (Bst P) (((toUr P ρ).symm x : ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P)
  map_add' x y := by simp
  map_smul' c x := comm_mulV P c _

theorem toB_injective : Function.Injective (toB P ρ) := fun x y h =>
  (toUr P ρ).symm.injective (Subtype.ext ((TensorProduct.comm ℚ_[l] V (Bst P)).injective h))

end GlobalTheory.PstRank

namespace GlobalTheory.PstRank

theorem rank_DpstUr_le : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l), IsDomain (Bst P) → (∀ (K : FinExt l) (b b' : Bst P), b ≠ 0 → (∀ g : ↥(GK K), b * actSt P (g : GQ l) b' = actSt P (g : GQ l) b * b') → ∃ c : ↥(MaximalUnramifiedExtension l), (c : Om l) ∈ K.1 ∧ b' = algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c * b) → ∀ {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V] [FiniteDimensional ℚ_[l] V] (ρ : Representation LL ↥(GK K) V), Module.rank ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) ≤ finrank ℚ_[l] V := by
  intro l _ P hdom hreg K LL _ _ V _ _ _ _ _ ρ
  refine rank_le fun s hs => ?_
  choose F hF using fun i : ↥s => (mem_Dpst P ρ).mp ((toUr P ρ).symm (i : DpstUr P ρ)).2
  have hFd := fun i : ↥s => (F i).2
  let K' : FinExt l := supExt K ⟨⨆ i, (F i).1, inferInstance⟩
  have hKK' : K.1 ≤ K'.1 := le_sup_left
  have hFK' : ∀ i, (F i).1 ≤ K'.1 := fun i => (le_iSup (fun i => (F i).1) i).trans le_sup_right
  let v : ↥s → Bst P ⊗[ℚ_[l]] V := fun i => toB P ρ (i : DpstUr P ρ)
  have hv : ∀ (g : ↥(GK K')) i, sigSt P ρ ⟨g, GK_le hKK' g.2⟩ (v i) = v i := by
    intro g i
    change sigSt P ρ _ (TensorProduct.comm ℚ_[l] V (Bst P) _) = _
    rw [sigSt_comm, hF i ⟨g, GK_le hKK' g.2⟩ (GK_le (hFK' i) g.2)]
    rfl
  have hli : LinearIndependent ↥(MaximalUnramifiedExtension l) v := hs.map' (toB P ρ) (LinearMap.ker_eq_bot.mpr (toB_injective P ρ))
  have hB : LinearIndepOn (Bst P) v ((Finset.univ : Finset ↥s) : Set ↥s) :=
    GlobalTheory.RegularRing.linearIndepOn_of_invariant (K := ↥(MaximalUnramifiedExtension l)) (B := Bst P) (G := ↥(GK K'))
      (fun g b => actSt P (g : GQ l) b)
      (fun g => (sigSt P ρ ⟨g, GK_le hKK' g.2⟩).toAddMonoidHom)
      (fun g b w => sigSt_smul P ρ _ b w)
      (fun b b' hb h => by
        obtain ⟨c, -, hc⟩ := hreg K' b b' hb h
        exact ⟨c, hc⟩)
      v hv Finset.univ (hli.linearIndepOn _)
  have hB' : LinearIndependent (Bst P) v := by
    rw [← linearIndepOn_univ]; rw [Finset.coe_univ] at hB; exact hB
  simpa using LinearIndependent.fintype_card_le_finrank hB'

end GlobalTheory.PstRank
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FockRowsOfFills
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

namespace GlobalTheory

theorem fock_rows_of_fills : ∀ (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (hT : GatTies D) (Y : LatInst D), FillsAll hT Y → (Y.Fl u w hg).t = D.R.t → ∀ (v : Fin (D.gat u w hg).P.nV) (s : Fin ((D.gat u w hg).P.n' v)) (i : ℕ), i < D.R.m → ∀ r : ℕ, ((FormalGroupSystem.nu (Y.Fl u w hg).t ((D.gat u w hg).P.lam0 v) ((Y.Fl u w hg).w v) (i + 1) s (r + 1) : ℤ) : ℝ) = if r < D.R.N i then DV.nuRow D u (i + 1) (hT.gat_pos u w hg ⟨v, s⟩) r else 0 := by
  intro D u w hg hT Y hF ht v s i hi r
  have hk : (D.gat u w hg).P.m + 1 = D.R.k := hT.gat_k u w hg
  have hw : ∀ b (hb : b < D.R.m), (((Y.Fl u w hg).w v (b + 1) s : ℤ) : ℝ) =
      ((D.hcW u (hT.gat_pos u w hg ⟨v, s⟩)).e ⟨b, hb⟩ : ℝ) - kaJ D (b + 1) := by
    intro b hb
    rw [hF u w hg v s (b + 1) (by simp [SizeData₂.lifts]; omega)]
    simp [wj, hb, D.hcW_e]
  have hwS : DV.wSz D (i + 1) (hT.gat_pos u w hg ⟨v, s⟩) = ((D.hcW u (hT.gat_pos u w hg ⟨v, s⟩)).e ⟨i, hi⟩ : ℝ) := by
    simp [DV.wSz, show 1 ≤ i + 1 ∧ i + 1 ≤ D.R.m by omega, D.hcW_e]
  unfold FormalGroupSystem.nu FormalGroupSystem.NN
  rw [ht]
  by_cases h1 : r < D.R.k
  · rw [if_pos (by omega), if_pos (show r < D.R.N i by simp [Ranks.N]; omega)]
    unfold FormalGroupSystem.lamI
    rw [dif_pos (by omega)]
    unfold DV.nuRow DV.srcPar
    rw [dif_pos h1, hwS]
    have hl : (((D.gat u w hg).P.lam0 v s ⟨r + 1 - 1, by omega⟩ : ℤ) : ℚ) =
        (D.hcW u (hT.gat_pos u w hg ⟨v, s⟩)).u ⟨r, h1⟩ - ((D.R.k : ℚ) - 1) / 2 + r := by
      rw [hT.gat_lam, (D.fm u).lam_eq 0 (Nat.zero_le _)]
      simp [hcToWeightQ, rhoVec, Ranks.N, h1]
      ring
    have hlR := congrArg (Rat.cast : ℚ → ℝ) hl
    push_cast at hlR ⊢
    rw [hlR, hw i hi]
    simp only [kaJ, Ranks.N, Nat.add_sub_cancel]
    push_cast
    ring
  · rw [if_neg (by omega)]
    obtain ⟨q, rfl⟩ : ∃ q, r = D.R.k + q := ⟨r - D.R.k, by omega⟩
    have hrk : D.R.k + q + 1 - ((D.gat u w hg).P.m + 2) = q := by omega
    rw [hrk]
    have ht1 : 0 < D.R.t + 1 := Nat.succ_pos _
    have hM : (i + 1) * (D.R.t + 1) = i * (D.R.t + 1) + (D.R.t + 1) := by ring
    have hNi : D.R.N i = D.R.k + i * (D.R.t + 1) := rfl
    by_cases h2 : q < i * (D.R.t + 1)
    · have hb : q / (D.R.t + 1) < i := by
        rw [Nat.div_lt_iff_lt_mul ht1]; exact h2
      rw [if_pos (by omega), if_pos (by omega)]
      unfold DV.nuRow DV.srcPar
      rw [dif_neg h1]
      simp only [Nat.add_sub_cancel_left]
      rw [dif_pos (by omega), hwS]
      have hr : q = q / (D.R.t + 1) * (D.R.t + 1) + q % (D.R.t + 1) := by
        have := Nat.div_add_mod q (D.R.t + 1); rw [mul_comm] at this; omega
      have hrR : (q : ℝ) = ((q / (D.R.t + 1) : ℕ) : ℝ) * ((D.R.t : ℝ) + 1) + ((q % (D.R.t + 1) : ℕ) : ℝ) := by
        exact_mod_cast hr
      push_cast
      rw [hw _ (by omega), hw i hi]
      simp only [kaJ, Ranks.N]
      push_cast
      rw [hrR]
      ring
    · rw [if_neg (show ¬ D.R.k + q < D.R.N i by omega)]
      by_cases h3 : q < i * (D.R.t + 1) + (D.R.t + 1)
      · have hb : q / (D.R.t + 1) = i := by
          apply le_antisymm
          · rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul ht1, Nat.succ_mul]; omega
          · rw [Nat.le_div_iff_mul_le ht1]; omega
        rw [if_pos (by omega), hb]
        simp
      · rw [if_neg (by omega)]
        simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharCmEqOneOfTrivialDegreeOneStatement
section
open NumberField IsDedekindDomain HeckeValGen GlobalTheory.HeckeSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_cm_eq_one_of_trivial_degree_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] [Algebra.IsQuadraticExtension F E] (χ : Ideles E →* ℂˣ), IsHeckeChar E χ → (∀ᶠ w in Filter.cofinite, DegOne F w → TrivAt χ w) → χ = 1 := by
  first | exact @GlobalTheory.HeckeSplit.heckeChar_eq_one_of_degOne | exact GlobalTheory.HeckeSplit.heckeChar_eq_one_of_degOne | (intros; apply GlobalTheory.HeckeSplit.heckeChar_eq_one_of_degOne <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralEigenCombination
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric Classical
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

namespace GlobalTheory.Proof.IntegralEigenCombination

theorem eigGen_integral_comb : ∀ (D : D7) (cD : D.what₂.Tau → ℂ), Formalism.L2.Ker.IsDgen D cD → ∀ (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]), ∀ τ : D.what₂.Tau, ∃ (n : ℕ) (r : Fin n → ℂ_[p]) (a : Fin n → D.host.E), (∀ j, ‖r j‖ ≤ 1) ∧ (∀ j, a j ∈ D.host.AA0) ∧ ∀ τ', ∑ j, r j * tauEmb D lm τ' (a j) = if τ' = τ then lamC lm (cD τ) else 0 := by
  intro D cD hD p _ lm τ
  obtain ⟨M, hMnf, hM, hs⟩ := hD
  obtain ⟨s, hsc, hsp⟩ := hs τ
  have hmem : s ∈ TaylorLogMetric.ellT D M τ := by rw [hsp]; exact Submodule.mem_span_singleton_self s
  have hv : (LinearMap.single (𝓞 M) (fun _ : D.what₂.Tau => (M : Type)) τ) s ∈ TaylorLogMetric.mmM D M :=
    Submodule.mem_comap.1 hmem
  obtain ⟨n, f, v, hfv⟩ := Submodule.mem_span_set'.1 hv
  have hva : ∀ j, ∃ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E),
      (v j : D.what₂.Tau → M) = fun τ => TaylorLogMetric.liftM M (TaylorLogMetric.embT D τ a) := fun j => (v j).2
  choose a ha hav using hva
  obtain ⟨g, hg⟩ := GlobalTheory.Proof.DirectionalDerivative.exists_lamHom lm (algebraMap M ℂ)
  have hg' : ∀ x : M, lamC lm (x : ℂ) = g x := hg
  refine ⟨n, fun j => g ((f j : 𝓞 M) : M), a, fun j => ?_, ha, fun τ' => ?_⟩
  · exact GlobalTheory.SplitEmbSep.norm_le_one_of_isIntegral (map_isIntegral_int g (f j).isIntegral_coe)
  · have e : ∀ j, tauEmb D lm τ' (a j) = g (TaylorLogMetric.liftM M (TaylorLogMetric.embT D τ' (a j))) := by
      intro j
      rw [← hg', TaylorLogMetric.liftM, dif_pos (hM _ _)]
      rfl
    have hc := congrFun hfv τ'
    simp only [Finset.sum_apply, Pi.smul_apply, hav] at hc
    simp only [e, ← map_mul]
    rw [← map_sum]
    have hc' : (∑ j, ((f j : 𝓞 M) : M) * TaylorLogMetric.liftM M (TaylorLogMetric.embT D τ' (a j))) =
        (LinearMap.single (𝓞 M) (fun _ : D.what₂.Tau => (M : Type)) τ) s τ' := by
      rw [← hc]; rfl
    rw [hc']
    by_cases h : τ' = τ
    · subst h; simp [hsc.symm, hg']
    · simp [h]
end GlobalTheory.Proof.IntegralEigenCombination
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrrTransferAbsIrr
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

noncomputable section
namespace GlobalTheory.IrrTransfer

open Matrix

theorem span_top_of_irred_algClosed {Γ : Type} [Group Γ] {k K : Type} [Field k] [Field K] [IsAlgClosed K]
    {r : ℕ} (hr : 1 ≤ r) (rb : Γ →* GL (Fin r) k) (ι : k →+* K)
    (h : ∀ W : Submodule K (Fin r → K), IsInv (mapRep ι rb) W → W = ⊥ ∨ W = ⊤) :
    Submodule.span k (Set.range fun g => (rb g : Matrix (Fin r) (Fin r) k)) = ⊤ := by
  letI : Algebra k K := ι.toAlgebra
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have hirr : IsIrrSub (mapRep ι rb) ⊤ :=
    ⟨top_ne_bot, fun _ _ _ => Submodule.mem_top, fun W _ hW => h W hW⟩
  have hs := GlobalTheory.BurnsideField.span_mat_eq_top_of_isIrrSub _ hirr
  apply GlobalTheory.BurnsideField.span_eq_top_of_span_map (K := K)
  convert hs using 3
  ext g a b
  simp [GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat, mapRep, RingHom.algebraMap_toAlgebra]

theorem span_image_top (k' : Type) [Field k'] (n : ℕ) :
    Submodule.span (AlgebraicClosure k')
      ((fun v : Fin n → k' => (algebraMap k' (AlgebraicClosure k')) ∘ v) ''
        ((⊤ : Submodule k' (Fin n → k')) : Set (Fin n → k'))) = ⊤ := by
  rw [eq_top_iff]
  intro u _
  rw [pi_eq_sum_univ' u]
  refine Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Pi.single a 1, trivial, ?_⟩)
  ext c
  by_cases hc : c = a
  · subst hc; simp
  · simp [Pi.single_eq_of_ne hc]

theorem absIrr_of_algClosed {Γ : Type} [Group Γ] {k K k' : Type} [Field k] [Field K] [IsAlgClosed K]
    [Field k'] {r : ℕ} (hr : 1 ≤ r) (rb : Γ →* GL (Fin r) k) (ι : k →+* K)
    (h : ∀ W : Submodule K (Fin r → K), IsInv (mapRep ι rb) W → W = ⊥ ∨ W = ⊤) (φ : k →+* k') :
    AbsIrrSub (mapRep φ rb) ⊤ := by
  have hsp := span_top_of_irred_algClosed hr rb ι h
  letI : Algebra k (AlgebraicClosure k') := ((algebraMap k' (AlgebraicClosure k')).comp φ).toAlgebra
  have hirr := GlobalTheory.BurnsideIff.eq_bot_or_top_of_span_eq_top (K := AlgebraicClosure k') _ hsp
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  rw [AbsIrrSub, span_image_top]
  refine ⟨top_ne_bot, fun _ _ _ => Submodule.mem_top, fun W _ hW => hirr W fun g v hv => ?_⟩
  have := hW g v hv
  simpa [mapRep, Matrix.map_map, RingHom.algebraMap_toAlgebra] using this

end GlobalTheory.IrrTransfer

namespace GlobalTheory.StringRepresentationDecomposition

theorem irr_transfer_absIrr : ∀ {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] {k k' : Type} [Field k] [Field k']
    {r : ℕ}, 1 ≤ r → ∀ (rb : Γ →* GL (Fin r) k) (ι : k →+* Formalism.CyclotomicNorms.Fbar l),
    Formalism.CyclotomicNorms.IrredOn (mapRep ι rb) ⊤ → ∀ φ : k →+* k', AbsIrrSub (mapRep φ rb) ⊤ := by
  intro l _ Γ _ k k' _ _ r hr rb ι h φ
  exact GlobalTheory.IrrTransfer.absIrr_of_algClosed hr rb ι (fun W hW => h W fun g _ v hv => hW g v hv) φ

end GlobalTheory.StringRepresentationDecomposition
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAlgebraicHeckeCharOfWeightOfIntegerExpo
section
noncomputable section

open NumberField Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.CuspRep GlobalTheory.CuspRep.InfType

namespace GlobalTheory.CuspRep.AlgExpo

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem dchi_atEmb (χ : HChar E) (τ : E →+* ℂ) (z : ℂ) :
    dchi χ (atEmb τ z) = expo χ τ * z + expo χ (ComplexEmbedding.conjugate τ) * starRingEnd ℂ z := by
  have e : atEmb τ (-Complex.I) = -atEmb τ Complex.I := by
    rw [atEmb_eq]; simp
  rw [atEmb_eq, map_add, map_smul, map_smul]
  simp only [expo, atEmb_conj, map_one, Complex.conj_I, e, map_neg, Complex.real_smul]
  conv_rhs => rw [← Complex.re_add_im z]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  linear_combination (z.im * dchi χ (atEmb τ Complex.I)) * Complex.I_mul_I

theorem dchi_eq_sum (χ : HChar E) (x : Cinf E) : dchi χ x = ∑ φ : E →+* ℂ, expo χ φ * coord φ x := by
  classical
  have hx : x = ∑ w : InfinitePlace E, atEmb w.embedding (x w) := by
    conv_lhs => rw [← Finset.univ_sum_single x]
    refine Finset.sum_congr rfl fun w _ => ?_
    unfold atEmb
    rw [InfinitePlace.mk_embedding, if_pos rfl]
  rw [hx, map_sum]
  simp only [map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [dchi_atEmb]
  simp only [coord_atEmb', mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]

theorem chiInf_eq_prod (χ : HChar E) (n : (E →+* ℂ) → ℤ) (hn : ∀ τ, expo χ τ = n τ) (u : (Cinf E)ˣ) :
    ((chiInf χ u : ℂˣ) : ℂ) = ∏ φ : E →+* ℂ, coord φ (u : Cinf E) ^ n φ := by
  rw [← expU_log u, chiInf_expU, dchi_eq_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun φ _ => ?_
  rw [coord_expU, hn, ← Complex.exp_int_mul]

theorem isAlgPos_of_expo : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (χ : HChar E)
    (n : (E →+* ℂ) → ℤ), (∀ τ, expo χ τ = n τ) → IsAlgPos χ n := by
  intro E _ _ _ χ n hn k _
  have e := chiInf_eq_prod χ n hn (Units.map (diagInf E).toMonoidHom k)
  rw [HChar.inf, MonoidHom.comp_apply, infDiag_eq]
  refine e.trans (Finset.prod_congr rfl fun φ _ => ?_)
  exact congrArg (· ^ n φ) (coord_algebraMap φ (k : E))

end GlobalTheory.CuspRep.AlgExpo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JumpWindowBlockExponentConditionOfJumpWindowStatement
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jumpWindowBlockExponentCondition_of_jumpWindow : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (h₁ : ℕ), D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d → D.R.t ≤ h₁ → GlobalTheory.BlockWindow.JumpWindow D i r π h₁ → GlobalTheory.BlockWindow.JointTB D HW F i r π h₁ h₁ (GlobalTheory.HubLoc.cBnum (D.nd.l i) h₁ D.R.t (4 * D.R.n * D.R.nV)) := by
  first | exact @GlobalTheory.BlockWindow.jointTB_of_jumpWindow | exact GlobalTheory.BlockWindow.jointTB_of_jumpWindow | (intros; apply GlobalTheory.BlockWindow.jointTB_of_jumpWindow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeJetsIntegralIffIntegralFrames
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric Classical
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

noncomputable section

namespace GlobalTheory.Proof.latticeJetsIntegral_iff_integralFrames

open MvPowerSeries GlobalTheory.Proof.DirectionalDerivative

section Formal

variable {p : ℕ} [Fact p.Prime] {σ κ : Type}

theorem jetsIntegral_iff (G : MvPowerSeries κ ℂ_[p]) :
    JetsIntegral G ↔ GlobalTheory.IndefiniteRowSideFullHecke.PolynomialIntegralityJets.JetsIntegral G := by
  unfold JetsIntegral GlobalTheory.IndefiniteRowSideFullHecke.PolynomialIntegralityJets.JetsIntegral GlobalTheory.IndefiniteRowSideFullHecke.PolynomialIntegralityJets.jetAt Formalism.DworkPowerSeriesWeights.mfact
  simp [Finsupp.prod, Nat.cast_prod]

theorem jetAt_linAt_list [Fintype σ] [Fintype κ] (c : σ → κ → ℂ_[p]) (l : List κ) (G : MvPowerSeries σ ℂ_[p]) :
    GlobalTheory.IndefiniteRowSideFullHecke.PolynomialIntegralityJets.jetAt (linAt c G) (l.map fun x => Finsupp.single x 1).sum =
      constantCoeff (l.foldl (fun H x => dirDer (fun k => c k x) H) G) := by
  induction l generalizing G with
  | nil => simp [jetAt_zero, constantCoeff_linAt]
  | cons x l ih =>
    rw [List.map_cons, List.sum_cons, add_comm, jetAt_add_single, pderiv_linAt, ih, List.foldl_cons]

end Formal

theorem jetsInt_frames : ∀ (D : D7) (N N' : ℕ) (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]), ∀ (Yl : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E)) (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]), (JetsInt D lm Yl F ↔ ∀ (n : ℕ) (y : Fin n → Matrix (Fin N') (Fin N) D.host.E), (∀ j, y j ∈ Yl) → JetsIntegral (atLin (fun k j => tauEmb D lm k.1 (y j k.2.1 k.2.2)) (fun j => MvPowerSeries.X j) F)) ∧ (JetsInt D lm Yl F → ∀ (ν : Type) [Fintype ν] (M : D.what₂.Tau × Fin N' × Fin N → ν → ℂ_[p]), (∀ x, ∃ (n : ℕ) (r : Fin n → ℂ_[p]) (y : Fin n → Matrix (Fin N') (Fin N) D.host.E), (∀ j, ‖r j‖ ≤ 1) ∧ (∀ j, y j ∈ Yl) ∧ ∀ k, M k x = ∑ j, r j * tauEmb D lm k.1 (y j k.2.1 k.2.2)) → JetsIntegral (atLin M (fun j => MvPowerSeries.X j) F)) := by
  intro D N N' p _ lm Yl F
  refine ⟨⟨fun hF n y hy => ?_, fun h n y hy => ?_⟩, fun hF ν _ M hM => ?_⟩
  · change JetsIntegral (linAt (fun k j => vecY D lm (y j) k) F)
    rw [jetsIntegral_iff]
    exact jetsIntegral_linAt _ (JetsInt D lm Yl) (fun G hG => jetsInt_const D lm Yl hG)
      (fun x G hG => keeps_vecY D lm Yl (hy x) G hG) F hF
  · have hJ := (jetsIntegral_iff _).1 (h n y hy)
    change GlobalTheory.IndefiniteRowSideFullHecke.PolynomialIntegralityJets.JetsIntegral (linAt (fun k j => vecY D lm (y j) k) F) at hJ
    have := hJ (((List.finRange n).reverse.map fun x => Finsupp.single x 1).sum)
    rw [jetAt_linAt_list, List.foldl_reverse] at this
    show ‖constantCoeff ((List.ofFn y).foldr (fun y' G => der D lm y' G) F)‖ ≤ 1
    rw [List.ofFn_eq_map, List.foldr_map]
    have hfun : (fun x G => der D lm (y x) G) = fun x G => dirDer (fun k => vecY D lm (y x) k) G := by
      funext x G
      exact der_eq D lm (y x) G
    rw [hfun]
    exact this
  · change JetsIntegral (linAt M F)
    rw [jetsIntegral_iff]
    refine jetsIntegral_linAt _ (JetsInt D lm Yl) (fun G hG => jetsInt_const D lm Yl hG) (fun x => ?_) F hF
    obtain ⟨n, r, y, hr, hy, hMx⟩ := hM x
    have e : (fun k => M k x) = ∑ j, r j • vecY D lm (y j) := by
      funext k
      rw [hMx k, Finset.sum_apply]
      rfl
    rw [e]
    exact Finset.sum_induction _ (Keeps D lm Yl) (fun _ _ ha hb => keeps_add D lm Yl ha hb) (keeps_zero D lm Yl)
      fun j _ => keeps_smul D lm Yl (hr j) (keeps_vecY D lm Yl (hy j))

end GlobalTheory.Proof.latticeJetsIntegral_iff_integralFrames
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormLeOfMemSq
section
open NumberField

noncomputable section

namespace GlobalTheory.EmbSepUnram

open GlobalTheory.Proof.IdempotentLatticeSequence (primeOf mem_primeOf primeOf_isMaximal natCast_mem_primeOf norm_int_le)

variable {p : ℕ} [Fact p.Prime]

theorem norm_sub_int_le {E : Type} [Field E] (φ ψ : E →+* ℂ_[p]) (y : 𝓞 E) : ‖φ (y : E) - ψ (y : E)‖ ≤ 1 :=
  by
  rw [sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (norm_int_le φ y) ?_)
  rw [norm_neg]; exact norm_int_le ψ y

theorem exists_algEquiv {K E : Type} [Field K] [Field E] [NumberField E] [Algebra K E] [IsGalois ℚ E]
    (ψ₁ ψ₂ : E →+* ℂ_[p]) (h : ∀ x : K, ψ₁ (algebraMap K E x) = ψ₂ (algebraMap K E x)) :
    ∃ σ : E ≃ₐ[K] E, ∀ x, ψ₁ x = ψ₂ (σ x) := by
  let _ : Algebra E ℂ_[p] := ψ₂.toAlgebra
  have _ := IsScalarTower.of_algebraMap_eq (R := ℚ) (S := E) (A := ℂ_[p]) fun x => by
    show algebraMap ℚ ℂ_[p] x = ψ₂ (algebraMap ℚ E x)
    rw [eq_ratCast (algebraMap ℚ ℂ_[p]), eq_ratCast (algebraMap ℚ E), map_ratCast]
  let τ : E ≃ₐ[ℚ] E := (ψ₁.toRatAlgHom).restrictNormal' E
  have hτ : ∀ x, ψ₂ (τ x) = ψ₁ x := fun x => (ψ₁.toRatAlgHom).restrictNormal_commutes E x
  let σ : E ≃ₐ[K] E := AlgEquiv.ofRingEquiv (f := τ.toRingEquiv) fun x => ψ₂.injective (by
    change ψ₂ (τ _) = _
    rw [hτ]; exact h x)
  exact ⟨σ, fun x => (hτ x).symm⟩

theorem norm_le_of_mem_sq {E : Type} [Field E] [NumberField E] (φ : E →+* ℂ_[p]) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ y : 𝓞 E, ‖φ (y : E)‖ < 1 → ‖φ (y : E)‖ ≤ r) {z : 𝓞 E} (hz : z ∈ primeOf φ ^ 2) :
    ‖φ (z : E)‖ ≤ r * r := by
  rw [pow_two] at hz
  refine Submodule.mul_induction_on hz (fun a ha b hb => ?_) (fun a b ha hb => ?_)
  · change ‖φ (algebraMap (𝓞 E) E (a * b))‖ ≤ r * r
    rw [map_mul, map_mul, norm_mul]
    exact mul_le_mul (h a ha) (h b hb) (norm_nonneg _) hr
  · change ‖φ (algebraMap (𝓞 E) E (a + b))‖ ≤ r * r
    rw [map_add, map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)

theorem embSep : Formalism.L2.Th1.GD.EmbSep := by
  intro p _ K E _ _ _ _ _ _ φ ψ₁ ψ₂ ⟨π, hπ1, hπ⟩ hK hφ hne
  by_contra hc
  push Not at hc
  have h1 : ∀ y : 𝓞 E, ‖ψ₂ (y : E) - ψ₁ (y : E)‖ < 1 := fun y => by
    have a := lt_of_le_of_ne (norm_sub_int_le φ ψ₁ y) (hc y)
    have e : ψ₂ (y : E) - ψ₁ (y : E) = (φ (y : E) - ψ₁ (y : E)) + -(φ (y : E) - ψ₂ (y : E)) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt a ?_)
    rw [norm_neg]; exact hφ y
  have hP : ∀ z : 𝓞 E, ‖ψ₂ (z : E)‖ < 1 → z ∈ primeOf φ := fun z hz => by
    change ‖φ (z : E)‖ < 1
    rw [← sub_add_cancel (φ (z : E)) (ψ₂ (z : E))]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (hφ z) hz)
  obtain ⟨σ, hσ⟩ := exists_algEquiv ψ₁ ψ₂ hK
  have : IsGalois K E := IsGalois.tower_top_of_isGalois ℚ K E
  have := primeOf_isMaximal φ
  have hP0 : primeOf φ ≠ ⊥ := fun h => by
    have := natCast_mem_primeOf φ
    rw [h, Ideal.mem_bot] at this
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast this)
  have : IsGaloisGroup (E ≃ₐ[K] E) (𝓞 K) (𝓞 E) := IsGaloisGroup.of_isFractionRing (E ≃ₐ[K] E) (𝓞 K) (𝓞 E) K E
  have hp0 : (primeOf φ).under (𝓞 K) ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot hP0

  set r := ‖φ (algebraMap K E (π : K))‖ with hr
  have hr0 : 0 < r := by
    refine lt_of_lt_of_le ?_ (hπ (p : 𝓞 E) (natCast_mem_primeOf φ))
    rw [norm_pos_iff]
    have : ((p : 𝓞 E) : E) = (p : E) := rfl
    rw [this, map_natCast]
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hsq : ¬ Ideal.map (algebraMap (𝓞 K) (𝓞 E)) ((primeOf φ).under (𝓞 K)) ≤ primeOf φ ^ 2 := fun hle => by
    have hπP : algebraMap (𝓞 K) (𝓞 E) π ∈ primeOf φ ^ 2 :=
      hle (Ideal.mem_map_of_mem _ (show algebraMap (𝓞 K) (𝓞 E) π ∈ primeOf φ from hπ1))
    have := norm_le_of_mem_sq φ hr0.le hπ hπP
    change r ≤ r * r at this
    nlinarith
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[K] E) ((primeOf φ).under (𝓞 K)) (primeOf φ)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx ((primeOf φ).under (𝓞 K)) (primeOf φ) (E ≃ₐ[K] E),
    ← Ideal.ramificationIdx'_eq_ramificationIdx ((primeOf φ).under (𝓞 K)) (primeOf φ) hp0,
    not_ne_iff.1 (mt (Ideal.ramificationIdx'_ne_one_iff Ideal.map_comap_le).1 hsq)] at hcard
  have hs : σ ∈ (primeOf φ).inertia (E ≃ₐ[K] E) := AddSubgroup.mem_inertia.2 fun x => hP _ (by
    change ‖ψ₂ (σ (x : E) - (x : E))‖ < 1
    rw [map_sub, ← hσ]
    exact h1 x |> fun h => by rwa [norm_sub_rev] at h)
  rw [Subgroup.eq_bot_of_card_eq _ hcard, Subgroup.mem_bot] at hs
  exact hne (RingHom.ext fun x => by rw [hσ, hs]; rfl)

end GlobalTheory.EmbSepUnram
end
end

