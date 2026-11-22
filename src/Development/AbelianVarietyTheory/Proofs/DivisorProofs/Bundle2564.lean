import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2451
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0585
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingPairingOnLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2403
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2452
import Development.AbelianVarietyTheory.Definitions.Divisors.StepsNonvacuous
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2453

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationBoundOfMulSqIntegral
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)

noncomputable section

namespace GlobalTheory.SizeSqIntegral

theorem sz_nat_val (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (D : ℕ) :
    Sz l lam (-(padicValNat l D : ℝ)) (D : ℂ) := by
  have h := GlobalTheory.SizeRat.sz_ratCast l lam (D : ℚ) (-(padicValNat l D : ℝ)) (by
    rw [padicValRat.of_nat]; simp)
  simpa using h

theorem sz_zero_of_isIntegral (l : ℕ) [hl : Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (x : ℂ)
    (h : IsIntegral ℤ x) : Sz l lam 0 x :=
  GlobalTheory.SzRules.sz_of_isIntegral 1 x (fun hd => hl.out.one_lt.ne' (Nat.dvd_one.1 hd)) (by simpa using h)

theorem main : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (D M : ℕ) (x : ℂ), 0 < D → IsIntegral ℤ ((D : ℂ) * x ^ 2) → Sz l lam (-(padicValNat l D : ℝ) / 2) ((D : ℂ) * x) ∧ Sz l lam (-(padicValNat l D : ℝ) / 2) ((M * l ^ padicValNat l D : ℕ) : ℂ) := by
  intro l hl lam D M x _ hx
  constructor
  · apply GlobalTheory.SzRules.sz_of_sq
    have h := GlobalTheory.SzRules.sz_mul (sz_nat_val l lam D) (sz_zero_of_isIntegral l lam _ hx)
    rw [add_zero] at h
    convert h using 1
    ring
  · have h1 := sz_nat_val l lam (l ^ padicValNat l D)
    rw [padicValNat.prime_pow] at h1
    have h2 : Sz l lam 0 (M : ℂ) := sz_zero_of_isIntegral l lam _ (by simpa using (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (M : ℤ))))
    have h := GlobalTheory.SzRules.sz_mul h2 h1
    rw [zero_add, ← Nat.cast_mul] at h
    refine GlobalTheory.SzRules.sz_mono ?_ h
    have : (0 : ℝ) ≤ (padicValNat l D : ℝ) := Nat.cast_nonneg _
    linarith

end GlobalTheory.SizeSqIntegral
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingPairingOnLatticeStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alternating_pairing_on_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
    ∀ (𝔞 𝔟 : FracId (FR E)) (P : E → E → FR E),
    (∀ x ∈ lattice c y, ∀ x' ∈ lattice c y, P x x' = -P x' x) →
    (∀ x₁ ∈ lattice c y, ∀ x₂ ∈ lattice c y, ∀ x' ∈ lattice c y, P (x₁ + x₂) x' = P x₁ x' + P x₂ x') →
    (∀ (a : 𝓞 (FR E)), ∀ x ∈ lattice c y, ∀ x' ∈ lattice c y, P (((a : FR E) : E) * x) x' = (a : FR E) * P x x') →
    (∀ x ∈ lattice c y, ∀ x' ∈ lattice c y, P x x' ∈ dualLat (𝔞 * 𝔟⁻¹)) →
    (∀ t ∈ dualLat (𝔞 * 𝔟⁻¹), t ∈ Submodule.span (𝓞 (FR E)) {t | ∃ x ∈ lattice c y, ∃ x' ∈ lattice c y, t = P x x'}) →
    ∃ ω₁ ω₂ : E, (∀ x, x ∈ lattice c y ↔ ∃ m ∈ dualLat 𝔞, ∃ β ∈ 𝔟.elt, x = (m : E) * ω₁ + (β : E) * ω₂) ∧
      ∀ m ∈ dualLat 𝔞, ∀ β ∈ 𝔟.elt, ∀ m' ∈ dualLat 𝔞, ∀ β' ∈ 𝔟.elt,
        P ((m : E) * ω₁ + (β : E) * ω₂) ((m' : E) * ω₁ + (β' : E) * ω₂) = β * m' - m * β' := by
  first | exact @GlobalTheory.AltLattice.main | exact GlobalTheory.AltLattice.main | (intros; apply GlobalTheory.AltLattice.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidConstantStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AmpleRigid
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ample_rigid_constant : GlobalTheory.AmpleRigid.ConstSt := by
  first | exact @GlobalTheory.AmpleRigid.constSt | exact GlobalTheory.AmpleRigid.constSt | (intros; apply GlobalTheory.AmpleRigid.constSt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidCubeStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AmpleRigid
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ample_rigid_cube : GlobalTheory.AmpleRigid.CubeSt := by
  first | exact @GlobalTheory.AmpleCube.cubeSt | exact GlobalTheory.AmpleCube.cubeSt | (intros; apply GlobalTheory.AmpleCube.cubeSt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidFiniteOrderStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AmpleRigid
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ample_rigid_finite_order : GlobalTheory.AmpleRigid.ConstSt → GlobalTheory.AmpleRigid.CubeSt → GlobalTheory.AmpleRigid.FiniteOrderSt := by
  first | exact @GlobalTheory.AmpleFiniteOrder.finiteOrder_of_const_of_cube | exact GlobalTheory.AmpleFiniteOrder.finiteOrder_of_const_of_cube | (intros; apply GlobalTheory.AmpleFiniteOrder.finiteOrder_of_const_of_cube <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidSeparatedStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AmpleRigid
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ample_rigid_separated : GlobalTheory.AmpleRigid.ConstSt → GlobalTheory.AmpleRigid.CubeSt → GlobalTheory.AmpleRigid.SeparatedSt := by
  first | exact @GlobalTheory.AmpleRigid.separatedSt_of_const_cube | exact GlobalTheory.AmpleRigid.separatedSt_of_const_cube | (intros; apply GlobalTheory.AmpleRigid.separatedSt_of_const_cube <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidSerreAmpleStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AmpleRigid
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ample_rigid_serre_ample : GlobalTheory.AmpleRigid.FiniteOrderSt → GlobalTheory.AmpleRigid.SeparatedSt → GlobalTheory.AmpleRigid.SerreAmpleSt := by
  first | exact @GlobalTheory.AmpleRigid.serreAmple_of_finiteOrder_of_separated | exact GlobalTheory.AmpleRigid.serreAmple_of_finiteOrder_of_separated | (intros; apply GlobalTheory.AmpleRigid.serreAmple_of_finiteOrder_of_separated <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticAtOfDifferentiableOnFin
section
set_option autoImplicit false

noncomputable section

open GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatJet.An GlobalTheory.RealMult
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum iterD polydisc)
open scoped Classical Topology

namespace GlobalTheory.LatJet.An

theorem analyticAt_of_differentiableOn_fin {I : Type} [Fintype I] {U : Set (I → ℂ)} (hU : IsOpen U)
    {f : (I → ℂ) → ℂ} (hf : DifferentiableOn ℂ f U) {z : I → ℂ} (hz : z ∈ U) : AnalyticAt ℂ f z := by
  let e : (Fin (Fintype.card I) → ℂ) ≃L[ℂ] (I → ℂ) :=
    ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : I => ℂ) (Fintype.equivFin I).symm
  have hs : AnalyticAt ℂ (⇑e.symm) z := (e.symm : (I → ℂ) →L[ℂ] (Fin (Fintype.card I) → ℂ)).analyticAt z
  have hU' : IsOpen (e ⁻¹' U) := hU.preimage e.continuous
  have hd : DifferentiableOn ℂ (f ∘ e) (e ⁻¹' U) := hf.comp e.differentiableOn (fun _ h => h)
  have ha : AnalyticAt ℂ (f ∘ e) (e.symm z) :=
    ReciprocityTheory.AnForm.Osgood.osgood _ _ _ hU' hd _ (by simpa using hz)
  exact (ha.comp hs).congr
    (Filter.Eventually.of_forall fun w => by simp)

theorem isOpen_polydisc (I : Type) [Fintype I] : IsOpen (polydisc I) := by
  simp only [polydisc, Set.setOf_forall]
  exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply i).norm continuous_const

theorem zero_mem_polydisc (I : Type) : (0 : I → ℂ) ∈ polydisc I := fun i => by simp

theorem jetAnalytic_of_steps (hC : JetCalc) (hCh : JetChain) (hG : GermEx) (hK : CoordEx) (hZ : JetZeta) (hD : JetDet)
    (hS : GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.Statement) : JetAnalytic := by
  obtain ⟨ε₀, hK⟩ := hK
  obtain ⟨s₀, hZ⟩ := hZ
  refine ⟨s₀ * ε₀, ?_⟩
  intro E _ _ _ I _ 𝔠 φ c y hf hCM hc R₀ s r m hs hr T n J Y _ hR₀ g ν u hg hu
  obtain ⟨G⟩ := hG E I 𝔠 φ c y hCM hc n T J Y
  obtain ⟨K⟩ := hK E I 𝔠 φ c y hCM hc n T J Y G
  have hζ := hZ ε₀ E I 𝔠 φ c y hCM hc n T J Y G K
  obtain ⟨hCan, hCe⟩ := hD ε₀ E I 𝔠 φ c y hCM hc n T J Y G K
  obtain ⟨-, hprod, hev, hconst, -, -, -⟩ := hC I n J
  have hgd : DifferentiableOn ℂ g (polydisc I) := ((((hS E I φ hf hCM).1 s hs).1 c y hc).1.2 g hg).1
  have hgan : AnalyticAt ℂ g 0 := analyticAt_of_differentiableOn_fin (isOpen_polydisc I) hgd (zero_mem_polydisc I)
  have hζan : AnalyticAt ℂ K.ζ 0 := by
    rw [analyticAt_pi_iff]
    intro i
    exact analyticAt_of_differentiableOn_fin K.isOpen (differentiableOn_pi.1 K.ζ_hol i) K.zero
  letI : Algebra R₀ G.B := ((algebraMap ℂ G.B).comp R₀.subtype).toAlgebra
  have hfan : AnalyticAt ℂ (fun z => G.y z (r.val G.B G.X trivial G.δ)) 0 :=
    analyticAt_of_differentiableOn_fin G.isOpen (G.hol _) G.zero
  have hfib : ∀ z ∈ K.V, K.C z ^ (2 * s) * G.y z (r.val G.B G.X trivial G.δ) = m * g (K.ζ z) := by
    intro z hz
    have hcomm : ∀ x : R₀, G.y z (algebraMap R₀ G.B x) = algebraMap R₀ ℂ x := fun x => by
      show G.y z (algebraMap ℂ G.B (x : ℂ)) = _
      rw [AlgHom.commutes]; rfl
    let σ : G.B →ₐ[R₀] ℂ := { (G.y z : G.B →+* ℂ) with commutes' := hcomm }
    have hb := r.baseChange G.B ℂ σ G.X trivial (K.X z) trivial (K.q z) G.δ (K.δ z) (K.pull z) (K.corr z)
    rw [← hr g hg (K.ζ z) (K.ζ_mem z hz) (K.X z) (K.U z hz) (K.δ z) (K.C z) (K.det z hz), hb]
    rfl
  have hjB : r.val J.B Y.X' trivial G.δ'' = G.j (r.val G.B G.X trivial G.δ) := by
    have hcomm : ∀ x : R₀, G.j (algebraMap R₀ G.B x) = algebraMap R₀ J.B x := fun x => by
      show G.j (algebraMap ℂ G.B (x : ℂ)) = _
      rw [AlgHom.commutes, hR₀]
    let σ : G.B →ₐ[R₀] J.B := { (G.j : G.B →+* J.B) with commutes' := hcomm }
    exact r.baseChange G.B J.B σ G.X trivial Y.X' trivial G.q G.δ G.δ'' G.pull G.corr
  have hhom := r.homog J.B Y.X' trivial G.δ'' Y.δ' G.e G.he
  have hpow : ∀ k : ℕ, jet J (fun z => K.C z ^ k) = jet J K.C ^ k := by
    intro k
    induction k with
    | zero => simpa using hconst 1
    | succ k ih =>
      have e1 : (fun z => K.C z ^ (k + 1)) = (fun z => K.C z ^ k) * K.C := by
        funext z; simp [pow_succ]
      rw [e1, (hprod (fun z => K.C z ^ k) K.C (hCan.pow k) hCan).1, ih, pow_succ]
  have hgζ : AnalyticAt ℂ (g ∘ K.ζ) 0 := by
    have : AnalyticAt ℂ g (K.ζ 0) := by rw [K.ζ_zero]; exact hgan
    exact this.comp hζan
  have hevq : (fun z => K.C z ^ (2 * s)) * (fun z => G.y z (r.val G.B G.X trivial G.δ)) =ᶠ[𝓝 0]
      (fun _ => m) * (g ∘ K.ζ) := by
    filter_upwards [K.isOpen.mem_nhds K.zero] with z hz using hfib z hz
  have hmain : algebraMap ℂ J.B (T.C ^ (2 * s)) * r.val J.B Y.X' trivial Y.δ' =
      algebraMap ℂ J.B m * jet J (g ∘ K.ζ) := by
    calc algebraMap ℂ J.B (T.C ^ (2 * s)) * r.val J.B Y.X' trivial Y.δ'
        = (G.e * jet J K.C) ^ (2 * s) * r.val J.B Y.X' trivial Y.δ' := by rw [map_pow, hCe]
      _ = jet J K.C ^ (2 * s) * (G.e ^ (2 * s) * r.val J.B Y.X' trivial Y.δ') := by ring
      _ = jet J (fun z => K.C z ^ (2 * s)) * jet J (fun z => G.y z (r.val G.B G.X trivial G.δ)) := by
        rw [hhom, hjB, G.jet_eq, hpow]
      _ = jet J ((fun z => K.C z ^ (2 * s)) * (fun z => G.y z (r.val G.B G.X trivial G.δ))) :=
        ((hprod (fun z => K.C z ^ (2 * s)) _ (hCan.pow _) hfan).1).symm
      _ = jet J ((fun _ => m) * (g ∘ K.ζ)) := hev _ _ hevq
      _ = algebraMap ℂ J.B m * jet J (g ∘ K.ζ) := by rw [(hprod _ _ analyticAt_const hgζ).1, hconst]
  have hrep := congrArg (fun x => J.b.repr x ν) hmain
  simp only [← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul] at hrep
  rw [hrep, hCh I n J K.ζ (fun i => (((s₀ * ε₀ : ℤˣ) : ℤ) : ℂ) * T.A i) g hζan K.ζ_zero hgan (fun i => hζ i) ν u hu]
  ring

end GlobalTheory.LatJet.An
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntitoneWeightLogBoundStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.antitone_weight_log_bound : Hypotheses2 → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → o ≤ 391 * (D.R.f * D.R.r * Lb) ^ 2 → ∀ la : AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → Real.log (∑ τ, ∑ k, |(la τ k : ℝ)|) ≤ 20 * Lb → ∀ Z, BergLe Z Y.U (fun _ => D.sp.W j) Y.dict la (Real.exp (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3)) ∧ SupBdWt Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z la (Real.exp (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3)) ∧ Real.log (Y.rkC la Z) ≤ C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3 := by
  first | exact @GlobalTheory.BergRank.berg_sup_rank | exact GlobalTheory.BergRank.berg_sup_rank | (intros; apply GlobalTheory.BergRank.berg_sup_rank <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppBijectiveOfFlatBaseChangeGlobalFunctionsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.app_bijective_of_flat_baseChange_globalFunctions : ∀ (R : Type) [CommRing R] (S Y Z : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), QuasiCompact π → QuasiSeparated π → Function.Bijective π.appTop.hom → Flat y → IsPullback p q y π → ∀ V : Y.Opens, Function.Bijective (p.app V).hom := by
  first | exact @GlobalTheory.Mum.app_bijective_of_flat_baseChange | exact GlobalTheory.Mum.app_bijective_of_flat_baseChange | (intros; apply GlobalTheory.Mum.app_bijective_of_flat_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveAffineOpenFlatBaseChangeProperStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.app_injective_affineOpen_flat_baseChange_proper : ∀ (R : Type) [CommRing R] (S Y Z : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsProper π → Flat y → IsPullback p q y π → Function.Injective π.appTop.hom → ∀ V : Y.Opens, IsAffineOpen V → Function.Injective (p.app V).hom := by
  first | exact @GlobalTheory.AffInj.app_injective_of_isPullback | exact GlobalTheory.AffInj.app_injective_of_isPullback | (intros; apply GlobalTheory.AffInj.app_injective_of_isPullback <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveDescentOfAffineOpensStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.app_injective_descent_of_affineOpens : ∀ (Y Z : Scheme.{0}) (p : Z ⟶ Y), (∀ V : Y.Opens, IsAffineOpen V → (Function.Injective (p.app V).hom ∧ ∀ f : Γ(Z, p ⁻¹ᵁ V), (∀ h : pullback.snd p p ⁻¹ᵁ (p ⁻¹ᵁ V) = pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V), ((pullback.fst p p).app _).hom f = ((pullback.snd p p).appLE _ _ h.ge).hom f) → f ∈ Set.range (p.app V).hom)) → ∀ V : Y.Opens, (Function.Injective (p.app V).hom ∧ ∀ f : Γ(Z, p ⁻¹ᵁ V), (∀ h : pullback.snd p p ⁻¹ᵁ (p ⁻¹ᵁ V) = pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V), ((pullback.fst p p).app _).hom f = ((pullback.snd p p).appLE _ _ h.ge).hom f) → f ∈ Set.range (p.app V).hom) := by
  first | exact @GlobalTheory.Mum.app_injective_and_descent_of_affineOpens | exact GlobalTheory.Mum.app_injective_and_descent_of_affineOpens | (intros; apply GlobalTheory.Mum.app_injective_and_descent_of_affineOpens <;> assumption)
end

