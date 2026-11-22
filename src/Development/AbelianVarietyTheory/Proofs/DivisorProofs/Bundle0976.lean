import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0950
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0944
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0912
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0724
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterFormula
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0951
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0952
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.LtChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfInAMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0932
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0937
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0933
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0511
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0505
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0183
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0133
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0138
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixTransvectionDiagonalDecomposition
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

namespace GlobalTheory.FormsLocus.VecGerm

theorem gs_map_sum {Y X : Scheme.{0}} (φ : Y ⟶ X) (z : Y) (U : X.Opens) (h : φ z ∈ U) {κ : Type} (t : Finset κ)
    (a b : κ → Γ(X, U)) : gs φ z U (∑ k ∈ t, a k * b k) = ∑ k ∈ t, gs φ z U (a k) * gs φ z U (b k) := by
  simp only [gs_eq φ z U h, map_sum, map_mul]

theorem germ_eq_sum_vecOf : ∀ (Rg : Type) [CommRing Rg] (A₀ X : Scheme.{0}) (f : A₀ ⟶ Sp Rg) (M : LB A₀) (Q : GlobalTheory.AbLaw.Perf f M) (s : LB.Sec M) (φ : X ⟶ A₀) (z : X) (i : Q.I), φ z ∈ Q.W i → gs φ z (M.U (Q.ch i)) (s.f (Q.ch i)) = ∑ k, gs φ z ⊤ (GlobalTheory.FormsLocus.cstT f (GlobalTheory.FormsLocus.vecOf Q s k)) * gs φ z (Q.W i) (Q.u k i) := by
  intro Rg _ A₀ X f M Q s φ z i hz
  have h := vecOf_spec Q s i
  have hz' : φ z ∈ (𝟙 A₀) ⁻¹ᵁ Q.W i := hz
  have h2 := congrArg (gs φ z ((𝟙 A₀) ⁻¹ᵁ Q.W i)) h
  rw [gs_map_sum φ z _ hz'] at h2
  have hl : gs φ z ((𝟙 A₀) ⁻¹ᵁ Q.W i) (GlobalTheory.AbLaw.rs A₀ (GlobalTheory.AbLaw.le_pull M (𝟙 A₀) (Q.le i))
      ((GlobalTheory.AbLaw.finSecPullId s).f (fun _ => Q.ch i))) = gs φ z (M.U (Q.ch i)) (s.f (Q.ch i)) := by
    unfold GlobalTheory.AbLaw.finSecPullId
    dsimp only
    exact (gs_res φ z _ hz' _).trans (gs_res φ z _ (GlobalTheory.AbLaw.le_pull M (𝟙 A₀) (Q.le i) hz') _)
  rw [hl] at h2
  rw [h2]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  · show gs φ z _ ((A₀.presheaf.map (homOfLE le_top).op).hom (cstT f (vecOf Q s k))) = _
    exact gs_res φ z le_top hz' _

end GlobalTheory.FormsLocus.VecGerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedLatticeColumnLatticeMulIffStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_completedLattice_columnLattice_mul_iff : ∀ (D : D7) {n : ℕ} (γ B : GL (Fin n) D.host.E), ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (γ * B)) ↔
      (γ⁻¹).1.map (eToEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat B) := by
  first | exact @GlobalTheory.LatMulAd.mem_hatL_colLat_mul | exact GlobalTheory.LatMulAd.mem_hatL_colLat_mul | (intros; apply GlobalTheory.LatMulAd.mem_hatL_colLat_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulFunEqOneOfEqOneOnMaxCompact
section
open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.FrameEquiv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameEquiv

set_option maxHeartbeats 1000000 in

theorem mulFun_eq_one_of_eq_one_on_maxCompact : ∀ (D : D7) (T : HSp D) (θ : InfFam D), IsInfFam θ → ∀ s : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ, (∀ τ, IsCartanInv (gramAt D T τ) (s τ)) → ∀ χ : GA D T → ℂ, (∀ u ∈ GinfC T, ∀ u' ∈ GinfC T, χ (u * u') = χ u * χ u') → (∀ k ∈ GinfC T, (∀ τ, compAt θ τ (Formalism.L2.Theta.mt T k) * s τ = s τ * compAt θ τ (Formalism.L2.Theta.mt T k)) → χ k = 1) → ∀ u ∈ GinfC T, χ u = 1 :=
  fun D T θ hθ s hs χ hm hK =>
    GlobalTheory.UnitaryChar.char_eq_one D θ T hθ s hs χ hm fun k hk h => hK k hk fun τ => (h τ).symm

end GlobalTheory.FrameEquiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaOperatorFrameSeriesOfStepsStatement
section
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nablaOperatorFrameSeries_of_steps : InvDerSt → LinSt → FrameSt → NabSt := by
  first | exact @GlobalTheory.IsoTriv.nabSt_of | exact GlobalTheory.IsoTriv.nabSt_of | (intros; apply GlobalTheory.IsoTriv.nabSt_of <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeDivisorsProdDistinctMonicIrreducibleStatement
section
open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natDegree_divisors_prod_distinct_monic_irreducible : ∀ (k : Type) [Field k] (ι : Type) [Fintype ι] (P : ι → k[X]), (∀ c, (P c).Monic ∧ Irreducible (P c)) → Function.Injective P → (∀ a : ℕ, (∃ q : k[X], q ∣ ∏ c, P c ∧ q.natDegree = a) ↔ ∃ A : Finset ι, ∑ c ∈ A, (P c).natDegree = a) ∧ ∀ Q : ℕ → Prop, (∃ q : k[X], Irreducible q ∧ q ∣ ∏ c, P c ∧ Q q.natDegree) ↔ ∃ c, Q (P c).natDegree := by
  first | exact @GlobalTheory.Div.natDegree_divisors_prod_distinct_monic_irreducible.natDegree_divisors_prod | exact GlobalTheory.Div.natDegree_divisors_prod_distinct_monic_irreducible.natDegree_divisors_prod | (intros; apply GlobalTheory.Div.natDegree_divisors_prod_distinct_monic_irreducible.natDegree_divisors_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeAlgebraMapStatement
section
open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.ChowHt GlobalTheory.Adelic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalizedPointHeightLattice_algebraMap : ∀ (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K] (N n : ℕ) (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), Submodule.span F (Set.range w.col) = ⊤ → (∀ σ, (A σ).det ≠ 0) → ∀ (K' : Type) [Field K'] [NumberField K'] [Algebra F K'] [Algebra K K'] [IsScalarTower F K K'] (y : Fin N → K), y ≠ 0 → pointHeight w A (fun j => algebraMap K K' (y j)) = pointHeight w A y := by
  first | exact @GlobalTheory.Adelic.HeightExt.pointHeight_algebraMap | exact GlobalTheory.Adelic.HeightExt.pointHeight_algebraMap | (intros; apply GlobalTheory.Adelic.HeightExt.pointHeight_algebraMap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeSmulStatement
section
open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.ChowHt GlobalTheory.Adelic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalizedPointHeightLattice_smul : ∀ (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K] (N n : ℕ) (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), Submodule.span F (Set.range w.col) = ⊤ → (∀ σ, (A σ).det ≠ 0) → ∀ (y : Fin N → K) (c : K), y ≠ 0 → c ≠ 0 → pointHeight w A (c • y) = pointHeight w A y := by
  first | exact @GlobalTheory.Adelic.HeightScaling.pointHeight_smul | exact GlobalTheory.Adelic.HeightScaling.pointHeight_smul | (intros; apply GlobalTheory.Adelic.HeightScaling.pointHeight_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbKEqZeroOfCharpolyNotSeparable
section
namespace GlobalTheory

theorem orbK_eq_zero_of_charpoly_not_separable (G : Type) [Group G] (k : Type) [Field k] (n : ℕ)
    (π : G →* GL (Fin n) k) (K : Subgroup G) (δ : G) (f : G → ℂ)
    (hf : ∀ g, f g ≠ 0 → ((π g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly.Separable)
    (hδ : ¬ ((π δ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly.Separable) :
    GlobalTheory.LKCount.orbK (MonoidHom.id G) K δ f = 0 := by
  unfold GlobalTheory.LKCount.orbK GlobalTheory.LKCount.orbC
  apply finsum_eq_zero_of_forall_eq_zero
  intro q
  have hz : ∀ x : G, f (x⁻¹ * δ * x) = 0 := by
    intro x
    by_contra h
    apply hδ
    have hs := hf _ h
    have hc : ((π (x⁻¹ * δ * x) : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly
        = ((π δ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly := by
      rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul,
        Matrix.charpoly_mul_comm, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    rwa [hc] at hs
  simp [hz]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodRingEmbeddingPropertiesStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.PMC GlobalTheory.AinfK GlobalTheory.AcrisK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_ring_embedding_properties : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ K : FinExt l, ∃ Ψ : BK K →+* P.R.BdR,
      (∀ c : ↥K.1, Ψ (inK K c) = algebraMap ↥K.1 P.R.BdR c) ∧
      (∀ (g : ↥(GK K)) (b : BK K), (P.PD K).actdR g (Ψ b) = Ψ (galB g b)) ∧
      (∀ b, Ψ b ∈ (P.PD K).Fil 0) ∧
      (∀ x : AK K, thetaK K x = 0 → Ψ (toB K (ofA K x)) ∈ (P.PD K).Fil 1) ∧
      (∀ x : AK K, thetaK K x = 0 → x ∉ RingHom.ker (thetaK K) ^ 2 → Ψ (toB K (ofA K x)) ∉ (P.PD K).Fil 2) := by
  first | exact @GlobalTheory.CrisToDR.exists_map | exact GlobalTheory.CrisToDR.exists_map | (intros; apply GlobalTheory.CrisToDR.exists_map <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlacesApart
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepLifts

theorem prime_eq_of_mem {K : Type} [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (h1 : (p : 𝓞 K) ∈ P.asIdeal) (h2 : (q : 𝓞 K) ∈ P.asIdeal) : p = q := by
  by_contra hne
  obtain ⟨a, b, hab⟩ : IsCoprime (p : 𝓞 K) (q : 𝓞 K) := Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 hne)
  exact P.isPrime.ne_top
    ((Ideal.eq_top_iff_one _).2 (hab ▸ add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)))

theorem places_apart {D : D7} {T : Type} (L : LevCh D T) {μ0 : T} (h : L.Is μ0) (t : T) :
    (∀ PP ∈ L.Pg, ∀ PP', PP' ∈ L.Pg ∨ PP' ∈ L.Q t → ¬ Lev.IsConjPl PP PP') ∧ Disjoint L.Pg (L.Q t) := by
  have hQ : ∀ PP ∈ L.Q t, ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := by
    intro PP hP k hk
    obtain ⟨⟨q, hq, hc, -, hne⟩, -⟩ := h.Q_pl t PP hP
    have h1 : (q : 𝓞 D.host.E) ∈ PP.asIdeal := by
      rw [← hc]
      exact Ideal.absNorm_mem PP.asIdeal
    exact hne k (prime_eq_of_mem PP hq (D.host.g_prime k) h1 hk)
  refine ⟨fun PP hP PP' hP' hc => ?_, Finset.disjoint_left.2 fun PP hP hP' => ?_⟩
  · rcases hP' with hP' | hP'
    · exact GlobalTheory.TypePlaces.not_isConjPl L.C.P L.Pg h.Pg PP hP PP' hP' hc
    · obtain ⟨k, hk⟩ := (h.Pg PP).1 hP
      obtain ⟨c, hc', e⟩ := hc _ (L.C.P.overP hk)
      have e' : c = ((D.host.g k : ℕ) : 𝓞 D.host.E) := RingOfIntegers.ext (by rw [e]; simp)
      exact hQ PP' hP' k (e' ▸ hc')
  · obtain ⟨k, hk⟩ := (h.Pg PP).1 hP
    exact hQ PP hP' k (L.C.P.overP hk)

theorem lifts_exist : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → ∀ (i : Fin D.R.m), (∀ (t : T) (g0 : G0 R.Pg D.R.r), ∃ κ, IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ) ∧ ∀ g0 : G0 R.Pg D.R.r, ∃ κ', IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ' := by
  intro D G _ _ Pl0 T A Ks _ _ _ R h i
  obtain ⟨c, hc⟩ := h.βV i
  obtain ⟨c', hc'⟩ := h.βW i
  refine ⟨fun t => ?_, ?_⟩
  · exact GlobalTheory.ParahoricLift.liftsExist (Vc D i) (R.βV i) (R.datVt i t) _ _ hc (places_apart _ h t).1 (places_apart _ h t).2
  · refine GlobalTheory.ParahoricLift.liftsExist (Wc D i) (R.βW i) (R.datWp i R.triv) _ _ hc' (fun PP hP PP' hP' => ?_)
      (Finset.disjoint_empty_right _)
    exact (places_apart _ h A.μ0).1 PP hP PP' (hP'.imp id fun h0 => absurd h0 (Finset.notMem_empty _))

end GlobalTheory.StepLifts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationModuleStatement
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex

namespace GlobalTheory.PolarisationModuleProof

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem gen_mul {L : Submodule (OF E) E} {l : ℕ} {ξ : E} (h : GenAt l (polMod L) ξ) :
    ∀ z ∈ polMod L * L, ∃ n : ℕ, n.Coprime l ∧ (n : E) * z ∈ mulLat ξ L := by
  intro z hz
  induction hz using Submodule.mul_induction_on' with
  | mem_mul_mem η hη x hx =>
    obtain ⟨n, hn, a, ha⟩ := h.2 η hη
    refine ⟨n, hn, Submodule.mem_map.2 ⟨a • x, L.smul_mem a hx, ?_⟩⟩
    rw [LinearMap.mulLeft_apply, Algebra.smul_def, ← mul_assoc, mul_comm ξ, ← ha]; ring
  | add z1 _ z2 _ h1 h2 =>
    obtain ⟨n1, hn1, h1⟩ := h1
    obtain ⟨n2, hn2, h2⟩ := h2
    refine ⟨n1 * n2, Nat.Coprime.mul hn1 hn2, ?_⟩
    have e : ((n1 * n2 : ℕ) : E) * (z1 + z2) = (n2 : OF E) • ((n1 : E) * z1) + (n1 : OF E) • ((n2 : E) * z2) := by
      rw [Algebra.smul_def, Algebra.smul_def]; push_cast; ring
    rw [e]
    exact add_mem (Submodule.smul_mem _ _ h1) (Submodule.smul_mem _ _ h2)

theorem trInt_of_isIntegral {x : E} (hx : IsIntegral ℤ x) : TrInt x := by
  have h := Algebra.isIntegral_trace (R := ℤ) (L := ℚ) (F := E) hx
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  exact ⟨n, by rw [← hn]; simp⟩

theorem isIntegral_of_mem_orderC {c : Ideal (OF E)} {x : E} (hx : x ∈ orderC c) : IsIntegral ℤ x := by
  obtain ⟨a, b, -, rfl⟩ := mem_orderC.1 hx
  refine IsIntegral.add ?_ ?_
  · exact (algebraMap (OF E) (𝓞 E) a).2
  · exact b.2

theorem invertible_of_isUnit {M : Submodule (OF E) E} (hU : IsUnit M) : Module.Invertible (OF E) M := by
  have h : Module.Invertible (OF E) ↥(↑hU.unit : Submodule (OF E) E) := inferInstance
  rwa [hU.unit_spec] at h

theorem sandwich_latMod {c : Ideal (OF E)} (hc : c ≠ ⊥) (y : (Af E)ˣ) :
    ∃ N : ℕ, 0 < N ∧ (∀ x : 𝓞 E, (N : E) * algebraMap (𝓞 E) E x ∈ latMod c y) ∧
      ∀ x ∈ latMod c y, IsIntegral ℤ ((N : E) * x) :=
  GlobalTheory.T.exists_denominator_of_adelic_lattice E c hc y

theorem modulePart {I : Type} (φ : I → E →+* ℂ) (hφ : IsCMType φ) (e₀ : ℤˣ) : ModulePart φ e₀ := by
  intro c hc y
  obtain ⟨N, hN, hO, hint⟩ := sandwich_latMod hc y
  obtain ⟨hU, hEq⟩ := GlobalTheory.T.polarization_module_unit_dual E (latMod c y) ⟨N, hN, hO, hint⟩
  have hanti : ∀ ξ ∈ polMod (latMod c y), IsCMField.complexConj E ξ = -ξ := fun ξ h => h.1
  have hFG : (dualLat (latMod c y)).toAddSubgroup.FG := hEq ▸ GlobalTheory.T.polarization_lattice_fg E (latMod c y) ⟨N, hN, hint⟩ hU
  refine ⟨invertible_of_isUnit hU, hEq, ?_, fun l hl => ⟨?_, fun ξ hξ hg => ?_⟩⟩
  · obtain ⟨ξ, hξ, hpos, -⟩ := GlobalTheory.T.exists_imaginary_generator_cm_type E (polMod (latMod c y)) hU hanti I φ hφ e₀ 2 Nat.prime_two
    exact ⟨ξ, hξ, hpos⟩
  · obtain ⟨ξ, hξ, hpos, hg⟩ := GlobalTheory.T.exists_imaginary_generator_cm_type E (polMod (latMod c y)) hU hanti I φ hφ e₀ l hl
    exact ⟨ξ, ⟨hξ, hpos⟩, hξ, hg⟩
  · have hle : mulLat ξ (latMod c y) ≤ dualLat (latMod c y) := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hz
      exact polMod_mul_le _ (Submodule.mul_mem_mul hg.1 hx)
    have h5 := GlobalTheory.T.relIndex_coprime_of_torsion (mulLat ξ (latMod c y)).toAddSubgroup (dualLat (latMod c y)).toAddSubgroup l hl hle hFG
      (fun z hz => by
        obtain ⟨n, hn, h⟩ := gen_mul hg z (hEq ▸ hz)
        exact ⟨n, hn, by rw [nsmul_eq_mul]; exact h⟩)
    exact ⟨hle, h5.1, h5.2⟩

theorem sizePart {I : Type} (φ : I → E →+* ℂ) (hφ : IsCMType φ) (e₀ : ℤˣ) : SizePart φ e₀ := by
  intro 𝔣 Q h𝔣 hQ l hl hQl y hy ξ hξ hg
  have hc : condQ 𝔣 Q ≠ ⊥ := by
    have : (𝔣 * ∏ q ∈ Q, q.asIdeal) ≠ 0 :=
      mul_ne_zero h𝔣.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)
    exact this
  obtain ⟨n, hn, hLO, hOL⟩ := GlobalTheory.T.adelic_lattice_order_coprime_index E (condQ 𝔣 Q) hc l hl y hy
  obtain ⟨N, hN, hO, hint⟩ := sandwich_latMod hc y
  obtain ⟨hU, hEq⟩ := GlobalTheory.T.polarization_module_unit_dual E (latMod (condQ 𝔣 Q) y) ⟨N, hN, hO, hint⟩
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
    obtain ⟨i, -, -⟩ := hφ σ
    have := hξ.2 i
    simp at this
  have hn1 : (n : E) ∈ dualLat (latMod (condQ 𝔣 Q) y) := by
    intro x hx
    have h1 := isIntegral_of_mem_orderC (hLO x hx)
    apply trInt_of_isIntegral
    have : (n : E) * bar x = bar ((n : E) * x) := by simp [bar]
    rw [this]
    exact map_isIntegral_int (IsCMField.complexConj E) h1
  rw [← hEq] at hn1
  obtain ⟨n', hn', hm⟩ := gen_mul hg _ hn1
  obtain ⟨x, hx, hxe⟩ := Submodule.mem_map.1 hm
  rw [LinearMap.mulLeft_apply] at hxe
  have hxi : IsIntegral ℤ ((n : E) * x) := isIntegral_of_mem_orderC (hLO x hx)
  have key : ((n' * n * n : ℕ) : E) * ξ⁻¹ = (n : E) * x := by
    have hx' : x = ((n' : E) * n) * ξ⁻¹ := by
      rw [← hxe, mul_comm ξ, mul_assoc, mul_inv_cancel₀ hξ0, mul_one]
    rw [hx']; push_cast; ring
  have hinv : ∀ σ : E →+* ℂ, IntAt l (σ ξ)⁻¹ := fun σ => ⟨n' * n * n,
    Nat.Coprime.mul (Nat.Coprime.mul hn' hn) hn, by
      rw [← map_inv₀, ← map_natCast σ, ← map_mul, key]; exact map_isIntegral_int σ hxi⟩
  refine ⟨hξ0, hinv, fun hdisc h𝔣l σ => ?_⟩
  have hcl : ∀ v : HeightOneSpectrum (OF E), v.asIdeal ∣ condQ 𝔣 Q → (l : OF E) ∉ v.asIdeal := by
    intro v hv
    rcases v.prime.dvd_or_dvd hv with h | h
    · exact h𝔣l v h
    · obtain ⟨q, hq, hvq⟩ := (Prime.dvd_finset_prod_iff v.prime _).1 h
      have : v.asIdeal = q.asIdeal :=
        ((q.isMaximal).eq_of_le v.isPrime.ne_top (Ideal.le_of_dvd hvq)).symm
      rw [this]; exact hQl q hq
  obtain ⟨m, hm, hmc⟩ := GlobalTheory.T.exists_coprime_integer_in_ideal (maximalRealSubfield E) (condQ 𝔣 Q) l hl hc hcl
  have hmO : ∀ b : 𝓞 E, (m : E) * algebraMap (𝓞 E) E b ∈ orderC (condQ 𝔣 Q) := by
    intro b
    refine mem_orderC.2 ⟨0, algebraMap (OF E) (𝓞 E) m * b,
      Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hmc), ?_⟩
    simp
  have hξL : ∀ b : 𝓞 E, ((n : E) * m) * algebraMap (𝓞 E) E b ∈ latMod (condQ 𝔣 Q) y := by
    intro b
    have := hOL _ (hmO b)
    rwa [← mul_assoc] at this
  have htr : ∀ b : 𝓞 E, ∃ k : ℤ, Algebra.trace ℚ E ((((n : E) * m) ^ 2 * ξ) * algebraMap (𝓞 E) E b) = k := by
    intro b
    obtain ⟨k, hk⟩ := hξ.1.2 _ (hξL b) _ (by simpa using hξL 1)
    refine ⟨k, ?_⟩
    rw [← hk]
    congr 1
    simp [bar]
    ring
  have h7 := GlobalTheory.T.discriminant_mul_trace_dual_integral E _ htr
  have h7' : IsIntegral ℤ (((discr E).natAbs : E) * (((n : E) * m) ^ 2 * ξ)) := by
    have hcast : ((discr E).natAbs : E) = (((discr E).natAbs : ℤ) : E) := (Int.cast_natCast _).symm
    rw [hcast, Int.natCast_natAbs]
    rcases abs_choice (discr E) with h | h <;> rw [h]
    · exact h7
    · push_cast; rw [neg_mul]; exact h7.neg
  refine ⟨(map_ne_zero σ).2 hξ0, ⟨(discr E).natAbs * (n * m) ^ 2, ?_, ?_⟩, hinv σ⟩
  · refine Nat.Coprime.mul ?_ (Nat.Coprime.pow_left 2 (Nat.Coprime.mul hn hm))
    exact Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hl).2 fun h => hdisc (Int.natCast_dvd.2 h))
  · have : (((discr E).natAbs * (n * m) ^ 2 : ℕ) : ℂ) * σ ξ = σ (((discr E).natAbs : E) * (((n : E) * m) ^ 2 * ξ)) := by
      rw [map_mul, map_mul, map_pow, map_mul]; simp only [map_natCast]; push_cast; ring
    rw [this]
    exact map_isIntegral_int σ h7'

theorem polarisationModule : PolarisationModule :=
  fun _ _ _ _ _ _ φ hφ e₀ => ⟨modulePart φ hφ e₀, sizePart φ hφ e₀⟩

end GlobalTheory.PolarisationModuleProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeBelowComplexEmbeddingLabelIsMaximalCardStatement
section
open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primeBelowComplexEmbeddingLabel_isMaximal_card : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p), ∀ τ : E →+* ℂ, (primeBelow io X τ).IsMaximal ∧ ∃ h : ℕ, 0 < h ∧ Nat.card (𝓞 E ⧸ primeBelow io X τ) = p ^ h := by
  first | exact @GlobalTheory.PrimePart.primeBelow_isMaximal_card | exact GlobalTheory.PrimePart.primeBelow_isMaximal_card | (intros; apply GlobalTheory.PrimePart.primeBelow_isMaximal_card <;> assumption)
end

