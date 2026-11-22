import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1447
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1451
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentApproximation.AddDense
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.FinitelyManyMarkedClassesTermDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0581
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1448
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1398
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1405
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1415
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1412
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1452
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0091
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0225
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1453
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1057
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import GroundTheory.GlobalFields.TateThesis.Bundle0006
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HeckeTateFunctionalEquation

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticGroupMatrixOfPreservesPhaseSpace
section
open scoped SchwartzMap Matrix

namespace GlobalTheory

open Matrix

theorem sympl_eq_neg_dotProduct_J {l : Type} [Fintype l] [DecidableEq l] (w w' : l ⊕ l → ℝ) :
    GlobalTheory.RealWeil.sympl w w' = -(w ⬝ᵥ (J l ℝ *ᵥ w')) := by
  simp only [GlobalTheory.RealWeil.sympl, GlobalTheory.RealWeil.pPart, GlobalTheory.RealWeil.qPart, J, EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, Fintype.sum_sum_type, fromBlocks_mulVec, Matrix.one_apply, Finset.sum_neg_distrib, mul_comm, Matrix.neg_mulVec, Matrix.one_mulVec]
  ring

theorem exists_symplecticGroup_of_sympl (l : Type) [Fintype l] [DecidableEq l]
    (ψ : (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ))
    (h : ∀ w w', GlobalTheory.RealWeil.sympl (ψ w) (ψ w') = GlobalTheory.RealWeil.sympl w w') :
    ∃ M : Matrix.symplecticGroup l ℝ, ∀ w, (M : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w = ψ w := by
  set M := LinearMap.toMatrix' ψ with hM
  have hMv : ∀ w, M *ᵥ w = ψ w := fun w => by rw [hM, LinearMap.toMatrix'_mulVec]
  have key : ∀ w w', w ⬝ᵥ ((Mᵀ * J l ℝ * M) *ᵥ w') = w ⬝ᵥ (J l ℝ *ᵥ w') := by
    intro w w'
    have := h w w'
    rw [sympl_eq_neg_dotProduct_J, sympl_eq_neg_dotProduct_J, ← hMv, ← hMv] at this
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
    linarith
  have hmem : M ∈ Matrix.symplecticGroup l ℝ := by
    rw [SymplecticGroup.mem_iff']
    ext i j
    have := key (Pi.single i 1) (Pi.single j 1)
    simpa [single_dotProduct, mulVec_single] using this
  exact ⟨⟨M, hmem⟩, hMv⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueArchimedeanMatrixAdeleExtensionOfCom
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.ArchMatCoords

theorem existsUnique_at_map_piInf :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {α β : Type}
    [Fintype α] [Fintype β] (τ : ∀ w : InfinitePlace F, EmbOver E w), IsCMExt F E σ →
    ∀ M : InfinitePlace F → Matrix α β ℂ, ∃! u : Matrix α β (AE F E), At (evI F) u ∧ ∀ w, u.map (piInf (τ w)) = M w := by
  intro F E _ _ _ _ _ σ α β _ _ τ hCM M
  have hex := fun i j => GlobalTheory.ThK.exists_at_evI_piInf_eq F E σ hCM τ (fun w => M w i j)
  choose z hzA hz using hex
  refine ⟨Matrix.of fun i j => z i j, ⟨?_, ?_⟩, ?_⟩
  · intro a ha
    ext i j
    simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.zero_apply]
    exact hzA i j a ha
  · intro w
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply]
    exact hz i j w
  · rintro v ⟨hvA, hvM⟩
    ext i j
    simp only [Matrix.of_apply]
    have hd : v i j - z i j = 0 := by
      refine GlobalTheory.ArchInj.eq_zero_of_at_of_piInf F E σ hCM τ _ ?_ ?_
      · intro a ha
        have h1 : (a • v) i j = 0 := by rw [hvA a ha]; rfl
        rw [Matrix.smul_apply] at h1
        rw [smul_sub, h1, hzA i j a ha, sub_zero]
      · intro w
        have h2 := congrFun (congrFun (hvM w) i) j
        rw [Matrix.map_apply] at h2
        rw [map_sub, h2, hz i j w, sub_self]
    exact sub_eq_zero.1 hd

end GlobalTheory.ArchMatCoords
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumPowersUnramifiedEtaTildeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weilDatum_powers_unramifiedEtaTilde : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (θ : InfFam D), IsInfFam θ → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ η, IsEtaTilde D η → ∃ om, IsWeilDatumO ψ S T (η ^ S.rank) (η ^ T.rank) om ∧ (∀ v ε, NonSplitAt D v ε → FixesVacAt ψ S T ΛS ΛT om v ε) ∧ VacCharPlus ψ θ S T om := by
  first | exact @GlobalTheory.WeilProduct.exists_weilDatum_etaTilde | exact GlobalTheory.WeilProduct.exists_weilDatum_etaTilde | (intros; apply GlobalTheory.WeilProduct.exists_weilDatum_etaTilde <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAbsMatrixProductLeHeights
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix

namespace GlobalTheory

theorem absFin_mul_mul_transpose_le : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ} (g : GL (Fin n) (AF F ⊗[F] E)) (X : Matrix (Fin n) (Fin d) (AF F ⊗[F] E)) (h : GL (Fin d) (AF F ⊗[F] E)) (v : HeightOneSpectrum (𝓞 F)) (i : Fin n) (j : Fin d), absFin F v (compFin F E v (((g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * X * (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E))ᵀ) i j)) ≤ htFin F v (bc (compFin F E v) g) * (Finset.univ.sup fun p : Fin n × Fin d => absFin F v (compFin F E v (X p.1 p.2))) * htFin F v (bc (compFin F E v) h) := by
  intro F E _ _ _ _ _ n d g X h v i j
  have hg : ∀ a b, ((bc (compFin F E v) g : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a b = compFin F E v ((g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) a b) := by
    intro a b; rfl
  have hh : ∀ a b, ((bc (compFin F E v) h : GL (Fin d) (Fv F v ⊗[F] E)) : Matrix (Fin d) (Fin d) (Fv F v ⊗[F] E)) a b = compFin F E v ((h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)) a b) := by
    intro a b; rfl
  have hG : ∀ a b, absFin F v (compFin F E v ((g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) a b)) ≤ htFin F v (bc (compFin F E v) g) := by
    intro a b
    have h1 := absFin_le_normFin F v ((bc (compFin F E v) g : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a b
    rw [hg] at h1
    exact h1.trans (le_htOf (normFin F v) _)
  have hH : ∀ a b, absFin F v (compFin F E v ((h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)) a b)) ≤ htFin F v (bc (compFin F E v) h) := by
    intro a b
    have h1 := absFin_le_normFin F v ((bc (compFin F E v) h : GL (Fin d) (Fv F v ⊗[F] E)) : Matrix (Fin d) (Fin d) (Fv F v ⊗[F] E)) a b
    rw [hh] at h1
    exact h1.trans (le_htOf (normFin F v) _)
  have hX : ∀ a b, absFin F v (compFin F E v (X a b)) ≤ Finset.univ.sup fun p : Fin n × Fin d => absFin F v (compFin F E v (X p.1 p.2)) := by
    intro a b
    exact Finset.le_sup (f := fun p : Fin n × Fin d => absFin F v (compFin F E v (X p.1 p.2))) (b := (a, b)) (Finset.mem_univ _)
  rw [Matrix.mul_apply, map_sum]
  refine absFin_sum_le F v _ _ fun l _ => ?_
  rw [Matrix.transpose_apply, Matrix.mul_apply, map_mul, map_sum]
  refine (absFin_mul_le F v _ _).trans (mul_le_mul' (absFin_sum_le F v _ _ fun k _ => ?_) (hH _ _))
  rw [map_mul]
  exact (absFin_mul_le F v _ _).trans (mul_le_mul' (hG _ _) (hX _ _))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdeleApproxScaled
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical

namespace GlobalTheory.EvAdm

theorem exists_rational_rep_scaledInt : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ r : κ → FiniteAdeleRing (𝓞 F) F, ∃ ξ : κ → F,
      r - (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a := by
  intro F _ _ κ _ a _ r
  have hd : DenseRange (Pi.map fun (_ : κ) => algebraMap F (FiniteAdeleRing (𝓞 F) F)) :=
    DenseRange.piMap fun _ => PI.UnipApproxD.IntegersDenseFiniteAdeles.denseRange (R := 𝓞 F) (K := F)
  have hop : IsOpen {y : κ → FiniteAdeleRing (𝓞 F) F | r - y ∈ GlobalTheory.EvAdm.scaledInt F κ a} :=
    (GlobalTheory.EvAdm.isOpen_scaledInt a).preimage (continuous_const.sub continuous_id)
  have hr : r ∈ {y : κ → FiniteAdeleRing (𝓞 F) F | r - y ∈ GlobalTheory.EvAdm.scaledInt F κ a} := by
    show r - r ∈ GlobalTheory.EvAdm.scaledInt F κ a
    rw [sub_self]
    exact zero_mem _
  obtain ⟨ξ, hξ⟩ := hd.exists_mem_open hop ⟨r, hr⟩
  exact ⟨ξ, hξ⟩

end GlobalTheory.EvAdm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitelyManyMarkedClassesTermDegreeOne
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.RootSumWeights.RegularPairCommutatorLemmas

theorem commComm_conj {S : Type} [Ring S] (u : S) (v : Sˣ)
    (h : ∀ a b : S, Commute a u → Commute b u → Commute a b) :
    ∀ a b : S, Commute a (v * u * v⁻¹) → Commute b (v * u * v⁻¹) → Commute a b := by
  intro a b ha hb
  have key : ∀ c : S, Commute c (v * u * v⁻¹) → Commute (((v⁻¹ : Sˣ) : S) * c * v) u := by
    intro c hc
    unfold Commute SemiconjBy at hc ⊢
    calc (((v⁻¹ : Sˣ) : S) * c * v) * u = ((v⁻¹ : Sˣ) : S) * (c * (v * u * ((v⁻¹ : Sˣ) : S))) * v := by
          simp [mul_assoc]
      _ = ((v⁻¹ : Sˣ) : S) * ((v * u * ((v⁻¹ : Sˣ) : S)) * c) * v := by rw [hc]
      _ = u * (((v⁻¹ : Sˣ) : S) * c * v) := by simp [mul_assoc]
  have h' := h _ _ (key a ha) (key b hb)
  unfold Commute SemiconjBy at h' ⊢
  have := congrArg (fun z => (v : S) * z * ((v⁻¹ : Sˣ) : S)) h'
  simpa [mul_assoc] using this

variable {p : ℕ} [Fact p.Prime]

theorem regAf_conj (G : HTGroup p) (g h : G.GAf) (hg : RegAf G g) : RegAf G (h⁻¹ * g * h) := by
  obtain ⟨w, hw⟩ := hg
  refine ⟨w, ?_⟩
  have e : ((ubcMap (AfP.eval w) (h⁻¹ * g * h)).1.1 : w.1.adicCompletion ℚ ⊗[ℚ] G.C) =
      (((ubcMap (AfP.eval w) h).1.1⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) *
        ((ubcMap (AfP.eval w) g).1.1 : w.1.adicCompletion ℚ ⊗[ℚ] G.C) *
        ((((ubcMap (AfP.eval w) h).1.1⁻¹)⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) := by
    simp [map_mul, map_inv]
  rw [e]
  exact commComm_conj _ _ hw

theorem commComm_tmul (G : HTGroup p) (K : Type) [Field K] [Algebra ℚ K] (γ : G.C)
    (hsep : (minpoly G.F γ).Separable) (hdeg : (minpoly G.F γ).natDegree = G.n) :
    ∀ a b : K ⊗[ℚ] G.C, Commute a ((1 : K) ⊗ₜ γ) → Commute b ((1 : K) ⊗ₜ γ) → Commute a b := by
  set Z := Subalgebra.centralizer ℚ ({γ} : Set G.C) with hZdef
  have hZ : ∀ x y : Z, x * y = y * x := by
    intro x y
    apply Subtype.ext
    have hc := GlobalTheory.CentSep.centralizer_eq_adjoin G.F G.C G.n G.rankC γ hsep hdeg
    have hx : ∀ g ∈ ({γ} : Set G.C), g * (x : G.C) = x * g := (Subalgebra.mem_centralizer_iff _).1 x.2
    have hy : ∀ g ∈ ({γ} : Set G.C), g * (y : G.C) = y * g := (Subalgebra.mem_centralizer_iff _).1 y.2
    show (x : G.C) * y = y * x
    have hy' : (y : G.C) ∈ Subalgebra.centralizer G.F ({γ} : Set G.C) := by
      rw [Subalgebra.mem_centralizer_iff]; exact hy
    rw [hc] at hy'
    have h2 := Algebra.adjoin_le_centralizer_centralizer G.F ({γ} : Set G.C) hy'
    rw [Subalgebra.mem_centralizer_iff] at h2
    have hx' : (x : G.C) ∈ Subalgebra.centralizer G.F ({γ} : Set G.C) := by
      rw [Subalgebra.mem_centralizer_iff]; exact hx
    exact h2 x hx'
  have hcomm : ∀ a b : K ⊗[ℚ] Z, a * b = b * a := by
    intro a b
    induction a using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [add_mul, mul_add, hx, hy]
    | tmul r x =>
      induction b using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => rw [add_mul, mul_add, hx, hy]
      | tmul s y => simp [Algebra.TensorProduct.tmul_mul_tmul, mul_comm r s, hZ x y]
  have hcen := Subalgebra.centralizer_coe_image_includeRight_eq_center_tensorProduct ℚ K G.C ({γ} : Set G.C)
  have mem : ∀ c : K ⊗[ℚ] G.C, Commute c ((1 : K) ⊗ₜ γ) →
      c ∈ (Algebra.TensorProduct.map (AlgHom.id ℚ K) Z.val).range := by
    intro c hc
    rw [← hcen, Subalgebra.mem_centralizer_iff]
    rintro _ ⟨g, hg, rfl⟩
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact hc.eq.symm
  intro a b ha hb
  obtain ⟨a', rfl⟩ := mem a ha
  obtain ⟨b', rfl⟩ := mem b hb
  unfold Commute SemiconjBy
  rw [← map_mul, ← map_mul, hcomm]

theorem regAf_pair (G : HTGroup p) (P : Pair G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) P.β x t) (h : G.GAf) : RegAf G (h⁻¹ * P.toAf x t hx P.self * h) := by
  apply regAf_conj
  obtain ⟨w⟩ := finitePlacesAway_nonempty p
  refine ⟨w, ?_⟩
  let φ := Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C)
  have e : ((ubcMap (AfP.eval w) (P.toAf x t hx P.self)).1.1 : w.1.adicCompletion ℚ ⊗[ℚ] G.C) =
      ((Units.map φ.toRingHom.toMonoidHom x : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) *
        ((1 : w.1.adicCompletion ℚ) ⊗ₜ (P.γ : G.C)) *
        (((Units.map φ.toRingHom.toMonoidHom x)⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) := by
    show φ ((x : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (P.γ : G.C) * ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)) = _
    rw [map_mul, map_mul]
    simp [φ, inC, Units.coe_map_inv]
  rw [e]
  exact commComm_conj _ _ (commComm_tmul G _ _ P.reg.2 P.reg.1)

end GlobalTheory.RootSumWeights.RegularPairCommutatorLemmas

namespace GlobalTheory.RootSumWeights.RegularPairCommutatorLemmas

theorem finitely_many_marked_classes_degree_one_of_regular (hI : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ (L : G.Level) (f : G.GAf → ℂ),
    IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → (∀ g, f g ≠ 0 → RegAf G g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
    Set.Finite {Q : Cls G | (∃ μ, (Quot.out Q).Mark μ) ∧ (Quot.out Q).term L.K.toSubgroup f 1 K' f' ≠ 0}) :
    GlobalTheory.RootSumWeights.FinitelyManyMarkedClassesTermDegreeOne := by
  intro p _ G ha L f K' f' hf hf'
  let f₀ : G.GAf → ℂ := fun g => if RegAf G g then f g else 0
  have hiff : ∀ (k g : G.GAf), RegAf G (k⁻¹ * g * k) ↔ RegAf G g := by
    intro k g
    refine ⟨fun h => ?_, fun h => regAf_conj G g k h⟩
    have := regAf_conj G _ k⁻¹ h
    simpa [mul_assoc] using this
  have hf₀ : IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f₀ := by
    obtain ⟨h1, h2, h3, S, hS⟩ := hf
    refine ⟨h1, h2, fun k hk g => ?_, S, fun g hg => hS g ?_⟩
    · have e := h3 k hk g
      simp only [MonoidHom.id_apply] at e ⊢
      simp only [f₀, e, hiff]
    · intro h; apply hg; simp [f₀, h]
  have hreg : ∀ g, f₀ g ≠ 0 → RegAf G g := fun g hg => by
    by_contra h; exact hg (by simp [f₀, h])
  have hterm : ∀ P : Pair G, P.term L.K.toSubgroup f 1 K' f' = P.term L.K.toSubgroup f₀ 1 K' f' := by
    intro P
    have key : ∀ x t hx δ z, P.termAt L.K.toSubgroup f 1 K' f' x t hx δ z =
        P.termAt L.K.toSubgroup f₀ 1 K' f' x t hx δ z := by
      intro x t hx δ z
      unfold Pair.termAt pointSum
      refine finsum_congr fun q => ?_
      have : f ((Quotient.out q).1⁻¹ * P.toAf x t hx P.self * (Quotient.out q).1) =
          f₀ ((Quotient.out q).1⁻¹ * P.toAf x t hx P.self * (Quotient.out q).1) := by
        simp only [f₀, if_pos (regAf_pair G P x t hx _)]
      rw [this]
    unfold Pair.term
    split_ifs <;> simp only [key]
  have hfin := hI p G ha L f₀ hf₀ hreg K' f' hf'
  simpa only [hterm] using hfin

end GlobalTheory.RootSumWeights.RegularPairCommutatorLemmas

theorem GlobalTheory.RootSumWeights.finitely_many_marked_classes_term_degree_one : GlobalTheory.RootSumWeights.FinitelyManyMarkedClassesTermDegreeOne := GlobalTheory.RootSumWeights.RegularPairCommutatorLemmas.finitely_many_marked_classes_degree_one_of_regular GlobalTheory.T.finite_markedPairClasses_degreeOne_term_ne_zero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockMapOfCanonicalCommutationPlacewiseSignature
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

noncomputable section

namespace GlobalTheory.CCRFock
open MvPolynomial

theorem atPl_linear_dep {W : Type} [Fintype W] [DecidableEq W] {Λ : W → Type} (w : W) :
    ∃ L : Module.End ℂ (MvPolynomial (Λ w) ℂ) →ₗ[ℂ] Module.End ℂ (⨂[ℂ] v : W, MvPolynomial (Λ v) ℂ),
      ∀ A, L A = GlobalTheory.RealLift.atPl (V := fun v : W => MvPolynomial (Λ v) ℂ) w A :=
  ⟨{ toFun := fun A => GlobalTheory.RealLift.atPl (V := fun v : W => MvPolynomial (Λ v) ℂ) w A
     map_add' := fun A B => by
       unfold GlobalTheory.RealLift.atPl
       exact PiTensorProduct.map_update_add
         (fun v : W => (LinearMap.id : MvPolynomial (Λ v) ℂ →ₗ[ℂ] MvPolynomial (Λ v) ℂ)) w A B
     map_smul' := fun c A => by
       unfold GlobalTheory.RealLift.atPl
       exact PiTensorProduct.map_update_smul
         (fun v : W => (LinearMap.id : MvPolynomial (Λ v) ℂ →ₗ[ℂ] MvPolynomial (Λ v) ℂ)) w c A }, fun _ => rfl⟩

theorem fock_map_of_ccr_dep : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {W : Type} [Fintype W] [DecidableEq W] {P Q R S : W → ℕ}
    (H : (∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) → Module.End ℂ V),
    (∀ c c', H (c + c') = H c + H c') → (∀ (r : ℝ) c, H ((r : ℂ) • c) = (r : ℂ) • H c) →
    (∀ c c', H c * H c' - H c' * H c =
      ((4 * Real.pi : ℂ) * Complex.I * ((∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im : ℂ)) • 1) →
    ∀ f₀ : V, f₀ ≠ 0 →
    (∀ w a b, H (Pi.single w (Matrix.single a b 1)) f₀ +
      (lineSign a b * Complex.I) • H (Pi.single w (Matrix.single a b Complex.I)) f₀ = 0) →
    ∃ Φ : (⨂[ℂ] w : W, Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)) →ₗ[ℂ] V, Function.Injective Φ ∧
      ∀ c T, Φ (sumPl (fun w => heisOp (c w)) T) = H c (Φ T) := by
  intro V _ _ W _ _ P Q R S H hadd hsmul hcomm f₀ hf₀ hvac
  obtain ⟨m, D, hm, hdm, hD0, hH⟩ := GlobalTheory.HoweD.ccr_fock_ops_sig H hadd hsmul hcomm
  obtain ⟨θ, hθ, hθ'⟩ := GlobalTheory.CCRFock.exists_polMapD W (fun w => Ix (P w) (Q w) × Ix (R w) (S w))
  have hd0 : ∀ j, D j f₀ = 0 := fun j => hD0 j f₀ (hvac j.1 j.2.1 j.2.2)
  have hD := GlobalTheory.CCRFock.polEval_pderiv m D hm f₀ (fun i j => by convert hdm i j) hd0
  refine ⟨polEval m hm f₀ ∘ₗ θ, ?_, ?_⟩
  · exact (GlobalTheory.FockAlg.injective_of_pderiv (polEval m hm f₀) D hD (by rw [polEval_one]; exact hf₀)).comp hθ
  · intro c T
    rw [hH c, Fintype.sum_sigma]
    simp only [LinearMap.comp_apply, sumPl, LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    obtain ⟨L, hL⟩ := atPl_linear_dep (W := W) (Λ := fun w => Ix (P w) (Q w) × Ix (R w) (S w)) w
    rw [heisOp_eq_sum_mul_pderiv, ← hL, map_sum]
    simp only [LinearMap.sum_apply, map_sum, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
    simp only [hL]
    refine Finset.sum_congr rfl fun l _ => ?_
    obtain ⟨hX, hY⟩ := hθ' w l T
    rw [hX, hY, polEval_X, hD]

end GlobalTheory.CCRFock
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankZetaKernelStatement
section
open MeasureTheory GlobalTheory.SplitFlip
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.full_rank_zeta_kernel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (n d : ℕ) (ν : kˣ →* ℂˣ), n ≤ d → GlobalTheory.SmGL.IsSmoothChar ν →
    ∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d,
    (∀ h : GL (Fin d) k, smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ (GlobalTheory.FullRankCoinv.Y0 k n d * h.val) = 0) →
      Ψ ∈ GlobalTheory.FullRankCoinv.augRk n d ν := by
  first | exact @GlobalTheory.FullRankCoinv.mem_augRk_of_fibre_eq_zero | exact GlobalTheory.FullRankCoinv.mem_augRk_of_fibre_eq_zero | (intros; apply GlobalTheory.FullRankCoinv.mem_augRk_of_fibre_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianMulMultilinearDiagonalMemSchwartzSubmodu
section
open MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.ConvSeries

theorem exists_mem_prod_mul_gauss {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (M : Submodule ℂ (SchwartzMap E ℂ))
    (hM : ∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ M → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ M)
    (G : SchwartzMap E ℂ) (hG : G ∈ M) :
    ∀ (m : ℕ) (ℓ : Fin m → E →L[ℝ] ℝ), ∃ t ∈ M, ∀ y, t y = (∏ i, ((ℓ i y : ℝ) : ℂ)) * G y := by
  intro m
  induction m with
  | zero => intro ℓ; exact ⟨G, hG, fun y => by simp⟩
  | succ m ih =>
    intro ℓ
    obtain ⟨t, ht, hty⟩ := ih (fun i => ℓ i.succ)
    have hg : (fun x : E => ((ℓ 0 x : ℝ) : ℂ)).HasTemperateGrowth :=
      (Complex.ofRealCLM.comp (ℓ 0)).hasTemperateGrowth
    refine ⟨SchwartzMap.smulLeftCLM ℂ (fun x : E => ((ℓ 0 x : ℝ) : ℂ)) t,
      hM (ℓ 0) t _ ht (fun x => by rw [SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul]), fun y => ?_⟩
    rw [SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul, hty, Fin.prod_univ_succ, mul_assoc]

theorem gauss_mul_diag_mem : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (M : Submodule ℂ (SchwartzMap E ℂ)),
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ M → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ M) →
    ∀ (c : ℝ), 0 < c →
    (∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M) →
    ∀ (k : ℕ) (B : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℂ),
      ∃ t ∈ M, ∀ y, t y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) * B (fun _ => y) := by
  intro E _ _ _ M hM c hc hGM k B
  have hin : ∀ x : E, innerSL ℝ x x = ‖x‖ ^ 2 := fun x => by
    first
    | rw [innerSL_apply_apply, real_inner_self_eq_norm_sq]
    | simp [real_inner_self_eq_norm_sq]
    | exact real_inner_self_eq_norm_sq x
  obtain ⟨G, hG⟩ := GlobalTheory.GaussSchwartz.exists_schwartz_exp_diag (-c • innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)
    (fun x hx => by
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]; rw [hin]
      have : 0 < ‖x‖ ^ 2 := by positivity
      nlinarith)
  have hG' : ∀ y, G y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) := fun y => by
    rw [hG, Complex.ofReal_exp]
    congr 1
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]; rw [hin]
    push_cast; ring
  have hGmem := hGM G hG'
  let b := stdOrthonormalBasis ℝ E
  have key : ∀ r : Fin k → Fin (Module.finrank ℝ E), ∃ t ∈ M,
      ∀ y, t y = (∏ j, ((innerSL ℝ (b (r j)) y : ℝ) : ℂ)) * G y :=
    fun r => exists_mem_prod_mul_gauss M hM G hGmem k (fun j => innerSL ℝ (b (r j)))
  choose t ht hty using key
  refine ⟨∑ r, B (fun j => b (r j)) • t r, M.sum_mem fun r _ => M.smul_mem _ (ht r), fun y => ?_⟩
  have hy : (fun _ : Fin k => y) = fun _ : Fin k => ∑ i, (inner ℝ (b i) y) • b i := by
    funext _; exact (b.sum_repr' y).symm
  rw [hy, ContinuousMultilinearMap.map_sum, Finset.mul_sum, SchwartzMap.sum_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [B.map_smul_univ (fun j => inner ℝ (b (r j)) y) (fun j => b (r j)), SchwartzMap.smul_apply, hty, hG',
    Complex.real_smul, smul_eq_mul]
  have hi : ∀ v : E, innerSL ℝ v y = inner ℝ v y := fun v => rfl
  simp only [hi]
  push_cast
  ring

end GlobalTheory.ConvSeries
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModelsDifferBySymplecticMatrixStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_models_differ_by_symplectic_matrix : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (ψ : AddChar (AF F) ℂ) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M M₁ : Model σ X W), M.IsGood ψ → M₁.IsGood ψ → ∃ a : Matrix ((Fin n × Fin d) ⊕ (Fin n × Fin d)) ((Fin n × Fin d) ⊕ (Fin n × Fin d)) F, aᵀ * Matrix.fromBlocks 0 1 (-1) 0 * a = Matrix.fromBlocks 0 1 (-1) 0 ∧ ∀ u, M₁.co.e u = ((a.map (algebraMap F (AF F)) *ᵥ Sum.elim (M.co.e u).1 (M.co.e u).2) ∘ Sum.inl, (a.map (algebraMap F (AF F)) *ᵥ Sum.elim (M.co.e u).1 (M.co.e u).2) ∘ Sum.inr) := by
  first | exact @GlobalTheory.goodModel_coords_rat_symplectic | exact GlobalTheory.goodModel_coords_rat_symplectic | (intros; apply GlobalTheory.goodModel_coords_rat_symplectic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarScalingNormAdditive
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.NormScaleHaar
open Formalism.UG GlobalTheory.AdelicU

theorem ideleModule_norm (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (t : (AE F E)ˣ) :
    ((GroundTheory.Global.IdeleGroup.ideleModule F (Units.map (Algebra.norm (AF F)) t) : ℝ)) = (absE F E t : ℝ) := by
  rw [GroundTheory.Global.IdeleGroup.ideleModule_eq, GlobalTheory.Doubling.absE_apply, NNReal.coe_mul, NNReal.coe_prod]
  have h := NNReal.toRealHom.toMonoidHom.map_finprod (GlobalTheory.Doubling.finite_mulSupport_absEv t)
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun w _ => ?_) (Eq.trans ?_ h.symm)
  · rw [GlobalTheory.Doubling.absEw_unitInf, NNReal.coe_pow, coe_nnnorm]
    rfl
  · refine finprod_congr fun v => ?_
    rw [GlobalTheory.Doubling.absEv_unitFin]
    rfl

end GlobalTheory.NormScaleHaar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTateFE
section
theorem GlobalTheory.Top.heckeTateFE : GlobalTheory.Published.HeckeTateFunctionalEquation :=
  GlobalTheory.CompanionTheory.HeckeFE.heckeTateFunctionalEquation
end

