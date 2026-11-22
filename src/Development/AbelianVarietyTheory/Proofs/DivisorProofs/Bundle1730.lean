import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1681
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpanRationalTranslatesVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaPullbackConstantSqEqDet
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0487
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTatePairingSandwich
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1700
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1703
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FramedFlatCoordinates
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPrincipalCongruenceLevelSubgroupIffIntegralCo
section
noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.FunObj.StdDatum

variable {D : D7}

theorem mul_mem_hatId {𝔪 : Ideal (𝓞 D.host.E)} {s x : AE D} (hs : s ∈ OhE D) (hx : x ∈ hatId D 𝔪) :
    s * x ∈ hatId D 𝔪 := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, t, ht, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨b, hb, s * t, mul_mem hs ht, by ring⟩
  | zero => rw [mul_zero]; exact zero_mem _
  | add _ _ _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
  | neg _ _ h => rw [mul_neg]; exact neg_mem h

theorem mem_hatId_mul {𝔪 : Ideal (𝓞 D.host.E)} {s x : AE D} (hs : s ∈ OhE D) (hx : x ∈ hatId D 𝔪) :
    x * s ∈ hatId D 𝔪 := by
  rw [mul_comm]; exact mul_mem_hatId hs hx

theorem congOne_mul {𝔪 : Ideal (𝓞 D.host.E)} {N : ℕ} {k k' : GA D N} (hk' : k' ∈ intG D N)
    (h : CongOne D 𝔪 k) (h' : CongOne D 𝔪 k') : CongOne D 𝔪 (k * k') := by
  intro i j
  have hi := (mem_intG k').1 hk'
  have e : (((k * k' : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) - 1 =
      ((((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) - 1) *
        ((k' : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))) +
      ((((k' : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))) - 1) := by
    simp only [Subgroup.coe_mul, Units.val_mul, sub_mul, one_mul]; abel
  rw [e, Matrix.add_apply, Matrix.mul_apply]
  exact add_mem (sum_mem fun l _ => mem_hatId_mul (hi l j).1 (h i l)) (h' i j)

theorem congOne_inv {𝔪 : Ideal (𝓞 D.host.E)} {N : ℕ} {k : GA D N} (hk : k ∈ intG D N)
    (h : CongOne D 𝔪 k) : CongOne D 𝔪 k⁻¹ := by
  intro i j
  have hi := (mem_intG k).1 hk
  have e : (((k⁻¹ : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) - 1 =
      -((((k : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) *
        ((((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))) - 1)) := by
    rw [Subgroup.coe_inv, mul_sub, Units.inv_mul, mul_one, neg_sub]
  rw [e, Matrix.neg_apply, Matrix.mul_apply]
  exact neg_mem (sum_mem fun l _ => mul_mem_hatId (hi i l).2 (h l j))

theorem congOne_one (𝔪 : Ideal (𝓞 D.host.E)) (N : ℕ) : CongOne D 𝔪 (1 : GA D N) := by
  intro i j
  simp only [OneMemClass.coe_one, Units.val_one, sub_self, Matrix.zero_apply]
  exact zero_mem _

theorem mem_congLev_iff : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (N : ℕ) (k : GA D N),
    k ∈ congLev D 𝔪 N ↔ k ∈ intG D N ∧ CongOne D 𝔪 k := by
  intro D 𝔪 N k
  refine ⟨fun h => ?_, fun h => Subgroup.subset_closure h⟩
  induction h using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => exact ⟨one_mem _, congOne_one 𝔪 N⟩
  | mul x y _ _ hx hy => exact ⟨mul_mem hx.1 hy.1, congOne_mul hy.1 hx.2 hy.2⟩
  | inv x _ hx => exact ⟨inv_mem hx.1, congOne_inv hx.1 hx.2⟩

end GlobalTheory.FunObj.StdDatum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemUnitaryRationalPointsOfFrameImagesRational
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem mem_ratPts_of_cols_rat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ (g : GAd σ J) (C' D' : Matrix (Fin n) (Fin j) E) (Z' : Matrix (Fin n) (Fin m) E), (matHom _ σ J g).1 * adMat F C = adMat F C' → (matHom _ σ J g).1 * adMat F Z = adMat F Z' → (matHom _ σ J g).1 * adMat F D = adMat F D' → g ∈ ratPts σ J := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF g C' D' Z' hC hZ hD
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
    Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F)
  dsimp only [adMat] at hC hZ hD
  set ι := inclR (F := F) (E := E) (AF F) with hι
  set x : Matrix (Fin n) (Fin n) E := C' * (cT (σ : E →+* E) D * J) + Z' * (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) +
    D' * (cT (σ : E →+* E) C * J) with hx
  have hM : (matHom _ σ J g).1 = x.map ι := by
    calc (matHom _ σ J g).1
        = (matHom _ σ J g).1 * (C * (cT (σ : E →+* E) D * J) + Z * (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) +
            D * (cT (σ : E →+* E) C * J)).map ι := by
          rw [hF.sum, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
      _ = x.map ι := by
          rw [hx]
          simp only [Matrix.map_add _ (map_add ι), Matrix.map_mul, Matrix.mul_add, ← Matrix.mul_assoc]
          rw [hC, hZ, hD]
  have hdet : x.det ≠ 0 := by
    haveI : Nontrivial (AF F ⊗[F] E) := ⟨⟨ι 0, ι 1, fun e => zero_ne_one (hinj e)⟩⟩
    intro h0
    have hu : IsUnit (x.map ι).det := by
      rw [← hM]; exact Matrix.isUnits_det_units _
    have h1 := ι.map_det x
    rw [h0, map_zero, RingHom.mapMatrix_apply] at h1
    rw [← h1] at hu
    exact not_isUnit_zero hu
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero x hdet, ?_, Units.ext hM.symm⟩
  show cT (σ : E →+* E) x * J * x = J
  apply Matrix.map_injective hinj
  have hg : cT (sigR (AF F) σ) (matHom _ σ J g).1 * JR (AF F) J * (matHom _ σ J g).1 = JR (AF F) J := g.2
  have hcT : cT (sigR (AF F) σ) (x.map ι) = (cT (σ : E →+* E) x).map ι := by
    ext a b; simp [Formalism.UG.cT, sigR, hι, inclR]
  rw [hM, hcT, JR, ← hι, ← Matrix.map_mul, ← Matrix.map_mul] at hg
  exact hg

end GlobalTheory.SphEis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OddEigenvectorUniqueUpToUnit
section
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

namespace GlobalTheory.VacuumUnique

theorem vacuum_unique : ∀ {D : D7}, Inp D → ∀ {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ}, Crv D cc δ → ∀ {N N' : ℕ} {e₁ e₂ : VC D N N' → ℂ}, oddE0 D cc δ t0 N N' e₁ → oddE0 D cc δ t0 N N' e₂ → e₁ ≠ 0 → ∃ κ : ℂ, ‖κ‖ = 1 ∧ e₂ = κ • e₁ := by
  intro D _ cc δ t0 hC N N' e₁ e₂ h₁ h₂ hne
  have hG1 := (GlobalTheory.InducedType.induced_type D).1
  have k0 : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') :=
    GlobalTheory.NormSum.VacMove.klat _ (GlobalTheory.NormSum.VacMove.moves_one D N) (GlobalTheory.NormSum.VacMove.moves_one D N')
  obtain ⟨hline, -⟩ := GlobalTheory.ThetaLine.theta_line D hG1 cc δ hC N N' _ k0
  obtain ⟨c, hc⟩ := hline e₂ h₂.1 e₁ h₁.1 hne
  refine ⟨c, ?_, hc⟩
  have hn := GlobalTheory.UnitaryTheta.normSq_ne_zero D cc δ hC k0 h₁.1 hne
  have e := h₂.2.2.1.trans h₁.2.2.1.symm
  rw [hc, GlobalTheory.UnitaryTheta.normSq_smul] at e
  have h1 : ‖c‖ ^ 2 = 1 := by
    have := mul_right_cancel₀ hn (e.trans (one_mul _).symm)
    exact this
  have h0 : 0 ≤ ‖c‖ := norm_nonneg c
  nlinarith [sq_nonneg (‖c‖ - 1), sq_nonneg (‖c‖ + 1)]

end GlobalTheory.VacuumUnique
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaLevelVPCore
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.LevelLawCore

theorem omega_level_vP_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (t : T0) (k : GA D (Vc D i)), VStd D i → k ∈ GfC (Vc D i) → ∀ hk : fin (Vc D i) k ∈ levJ R i t, R.ωP i t (k, 1) (R.vP i t) = (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ ⟨fin (Vc D i) k, hk⟩ : ℂˣ) : ℂ)⁻¹ • R.vP i t := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F h i t k _ hf hk
  have hl : Formalism.IndefR.Lev.finE (Vc D i) k ∈ Formalism.L2.DIV.lev D.sp.cm (Vc D i).gram (R.βV i)
      (Formalism.IndefR.Lev.flag1L (R.datVt i t)) := hk
  have hκ : Formalism.IndefR.Lev.IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) 1 k := ⟨hf, hl.1, Subgroup.mem_bot.1 hl.2⟩
  have hκ' : Formalism.IndefR.Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) 1 1 :=
    ⟨Subgroup.one_mem _, by rw [map_one]; exact Subgroup.one_mem _, by rw [map_one]; exact Formalism.L2.DIV.rTup_one⟩
  refine (GlobalTheory.T.weilAction_liftPair_stepVector_invLevelChar R h.lev h.models.inf h.thP.ωP h.thP.vP i t 1 k 1 hκ hκ').trans ?_
  exact congrArg (fun z : ℂˣ => (z : ℂ)⁻¹ • R.vP i t)
    (Formalism.IndefR.Lev.levFn_flag1 (V := Vc D i) (β := R.βV i) (L := R.datVt i t) (Formalism.IndefR.Lev.finE (Vc D i) k)).symm

end GlobalTheory.AdTh.LevelLawCore
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupExistsSmulMemSpanDlog
section
set_option autoImplicit false

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.PDivLat

theorem lie_eq_zero_of_dlog {p : ℕ} [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] (hv : v.Integers O)
    {ε : PreTilt O p} {hε : IsPrimitiveSystem ε} {G : PDivGroup p O} (hD : HasDatum hε G)
    (x : G.Lie) (hx : ∀ χ, x (dlog G χ) = 0) : x = 0 := by
  haveI : IsIntegrallyClosedIn O C := isIntegrallyClosedIn_iff.2 ⟨hv.hom_inj, fun h =>
    hv.exists_of_le_one (hv.isIntegral_iff_v_le_one.1 h)⟩
  obtain ⟨D, e, fil, lie, -, hb⟩ := hD
  have hG : Function.Surjective (G.pairing O).flip := (G.pairing_flip_bijective C).2
  have h0 : bQuot D (lie.symm x) = 0 :=
    GlobalTheory.DetInv.HTKer.pairingO_inj (hε := hε) hG e _ _ fun χ => by
      rw [hb, hx]; simp [pairingO]
  obtain ⟨m, hm⟩ := D.Fil.mkQ_surjective (lie.symm x)
  have h1 : D.bb m = 0 := by
    rw [← hm] at h0; exact h0
  have h2 : lie.symm x = 0 := by
    rw [← hm, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact h1
  simpa using congrArg lie h2

theorem exists_smul_mem_span_dlog : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ G : PDivGroup p O, HasDatum hε G → ∃ c : O, c ≠ 0 ∧ ∀ w : G.omega, c • w ∈ Submodule.span O (Set.range (dlog G)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G hD
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  haveI : Module.Finite O G.omega := (GlobalTheory.PDiv.omega_finite_projective p C v O hv G).1
  set S := Submodule.span O (Set.range (dlog G)) with hS
  let T := Submodule.torsion O (G.omega ⧸ S)
  let π : G.omega →ₗ[O] (G.omega ⧸ S) ⧸ T := T.mkQ ∘ₗ S.mkQ
  have hπ : Function.Surjective π := T.mkQ_surjective.comp S.mkQ_surjective
  haveI : Module.Flat O ((G.omega ⧸ S) ⧸ T) := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout]
    exact Submodule.QuotientTorsion.torsion_eq_bot
  haveI : Module.Free O ((G.omega ⧸ S) ⧸ T) := Module.free_of_flat_of_isLocalRing
  let b := Module.Free.chooseBasis O ((G.omega ⧸ S) ⧸ T)
  have hcoord : ∀ i, b.coord i ∘ₗ π = 0 := fun i =>
    lie_eq_zero_of_dlog C hv hD _ fun χ => by
      change b.coord i (T.mkQ (S.mkQ (dlog G χ))) = 0
      have hs : S.mkQ (dlog G χ) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact Submodule.subset_span ⟨χ, rfl⟩
      rw [hs, map_zero, map_zero]
  have hzero : ∀ q : (G.omega ⧸ S) ⧸ T, q = 0 := fun q => by
    obtain ⟨w, rfl⟩ := hπ q
    refine b.ext_elem fun i => ?_
    have := LinearMap.congr_fun (hcoord i) w
    simpa using this
  have htor : Module.IsTorsion O (G.omega ⧸ S) := fun q => by
    have := hzero (T.mkQ q)
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_torsion_iff] at this
    exact this
  obtain ⟨c, hc, hc0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors htor
  refine ⟨c, nonZeroDivisors.ne_zero hc0, fun w => ?_⟩
  have := Submodule.mem_annihilator.1 hc (S.mkQ w) Submodule.mem_top
  rwa [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this

end GlobalTheory.PDivLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PackingCountInequivalentDiscreteSubgroup
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

open scoped Pointwise

namespace GlobalTheory.Packing

theorem mem_smul_smul_iff {G : Type} [Group G] (Λ : Subgroup G) (γ : Λ) (t x : G) (U : Set G) :
    x ∈ γ • (t • U) ↔ t⁻¹ * ((γ : G)⁻¹ * x) ∈ U := by
  rw [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_smul_set_iff_inv_smul_mem]
  simp [Subgroup.smul_def, smul_eq_mul]

theorem packing_count : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ Λ : Subgroup G) [Countable Λ] (μ : Measure G) (D U : Set G), Λ ≤ Γ → (∀ K : Set G, IsCompact K → (K ∩ Γ).Finite) → μ.IsHaarMeasure → IsFundamentalDomain Λ D μ → IsCompact U → ∃ k : ℕ, ∀ (T : Finset G) (S : Set G), (∀ t ∈ T, t ∈ Γ) → (∀ t ∈ T, ∀ t' ∈ T, t' * t⁻¹ ∈ Λ → t = t') → MeasurableSet S → (∀ γ ∈ Λ, ∀ x ∈ S, γ * x ∈ S) → (∀ t ∈ T, ∀ u ∈ U, t * u ∈ S) → T.card * μ U ≤ k * μ (S ∩ D) := by
  intro G _ _ _ _ _ _ _ _ Γ Λ _ μ D U hΛΓ hdisc hHaar hD hU
  have hUc : IsCompact (U * U⁻¹) := hU.mul hU.inv
  have hfin : (U * U⁻¹ ∩ (Γ : Set G)).Finite := hdisc _ hUc
  refine ⟨hfin.toFinset.card, ?_⟩
  intro T S hTΓ hTdist hS hSinv hTS
  have hUm : MeasurableSet U := hU.isClosed.measurableSet
  have hmeasA : ∀ (γ : Λ) (t : G), MeasurableSet (γ • (t • U)) := by
    intro γ t
    have : γ • (t • U) = (fun y => t⁻¹ * ((γ : G)⁻¹ * y)) ⁻¹' U := by
      ext y; rw [mem_smul_smul_iff]; rfl
    rw [this]
    exact hUm.preimage (continuous_const.mul (continuous_const.mul continuous_id)).measurable
  have hsubS : ∀ (γ : Λ), ∀ t ∈ T, γ • (t • U) ⊆ S := by
    intro γ t ht y hy
    rw [mem_smul_smul_iff] at hy
    have h1 := hSinv (γ : G) γ.2 _ (hTS t ht _ hy)
    simpa [mul_assoc] using h1
  set ν := μ.restrict (S ∩ D) with hν
  have key : ∀ t ∈ T, μ U = ∑' γ : Λ, ∫⁻ x, (γ • (t • U)).indicator 1 x ∂ν := by
    intro t ht
    rw [← measure_smul μ t U, hD.measure_eq_tsum (t • U)]
    refine tsum_congr fun γ => ?_
    rw [lintegral_indicator_one (hmeasA γ t), hν, Measure.restrict_apply (hmeasA γ t)]
    congr 1
    ext y
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, hsubS γ t ht h1, h2⟩
    · rintro ⟨h1, _, h2⟩; exact ⟨h1, h2⟩
  have hpt : ∀ x : G, ∑ t ∈ T, ∑' γ : Λ, (γ • (t • U)).indicator (1 : G → ℝ≥0∞) x
      ≤ (hfin.toFinset.card : ℝ≥0∞) := by
    intro x
    classical
    have hswap : ∑ t ∈ T, ∑' γ : Λ, (γ • (t • U)).indicator (1 : G → ℝ≥0∞) x
        = ∑' γ : Λ, ∑ t ∈ T, (γ • (t • U)).indicator (1 : G → ℝ≥0∞) x := by
      first
      | exact (Summable.tsum_finsetSum fun _ _ => ENNReal.summable).symm
      | exact (tsum_sum fun _ _ => ENNReal.summable).symm
      | exact (ENNReal.tsum_finsetSum _ _).symm
    rw [hswap, ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun s => ?_
    have hbool : ∑ γ ∈ s, ∑ t ∈ T, (γ • (t • U)).indicator (1 : G → ℝ≥0∞) x
        = (((s ×ˢ T).filter (fun p : Λ × G => x ∈ p.1 • (p.2 • U))).card : ℝ≥0∞) := by
      rw [Finset.card_filter, Finset.sum_product]
      push_cast
      simp only [Set.indicator_apply, Pi.one_apply]
    rw [hbool]
    have hcard : ((s ×ˢ T).filter (fun p : Λ × G => x ∈ p.1 • (p.2 • U))).card
        ≤ hfin.toFinset.card := by
      set P := (s ×ˢ T).filter (fun p : Λ × G => x ∈ p.1 • (p.2 • U)) with hPdef
      have memP : ∀ p : Λ × G, p ∈ P → p.2 ∈ T ∧ x ∈ p.1 • (p.2 • U) := by
        intro p hp
        rw [hPdef, Finset.mem_filter, Finset.mem_product] at hp
        exact ⟨hp.1.2, hp.2⟩
      rcases P.eq_empty_or_nonempty with hP | ⟨p₀, h₀⟩
      · rw [hP]; exact Nat.zero_le _
      obtain ⟨ht₀, hx₀⟩ := memP p₀ h₀
      rw [mem_smul_smul_iff] at hx₀
      refine Finset.card_le_card_of_injOn
        (fun p : Λ × G => (p₀.2⁻¹ * (p₀.1 : G)⁻¹) * ((p.1 : G) * p.2)) ?_ ?_
      · intro p hp
        have hp' : p ∈ P := by first | exact Finset.mem_coe.1 hp | exact hp
        obtain ⟨ht, hx⟩ := memP p hp'
        rw [mem_smul_smul_iff] at hx
        show _ ∈ (hfin.toFinset : Set G)
        rw [Set.Finite.coe_toFinset]
        refine ⟨?_, ?_⟩
        · refine Set.mem_mul.2 ⟨_, hx₀, (p.2⁻¹ * ((p.1 : G)⁻¹ * x))⁻¹, ?_, ?_⟩
          · rw [Set.mem_inv, inv_inv]; exact hx
          · group
        · exact Γ.mul_mem (Γ.mul_mem (Γ.inv_mem (hTΓ _ ht₀)) (Γ.inv_mem (hΛΓ p₀.1.2)))
            (Γ.mul_mem (hΛΓ p.1.2) (hTΓ _ ht))
      · intro p hp q hq hpq
        have hp' : p ∈ P := by first | exact Finset.mem_coe.1 hp | exact hp
        have hq' : q ∈ P := by first | exact Finset.mem_coe.1 hq | exact hq
        have hpT := (memP p hp').1
        have hqT := (memP q hq').1
        have h1 : (p.1 : G) * p.2 = (q.1 : G) * q.2 := mul_left_cancel hpq
        have e : q.2 * p.2⁻¹ = (q.1 : G)⁻¹ * p.1 := by
          rw [mul_inv_eq_iff_eq_mul, mul_assoc, h1, ← mul_assoc, inv_mul_cancel, one_mul]
        have htt : p.2 = q.2 := hTdist _ hpT _ hqT (e ▸ Λ.mul_mem (Λ.inv_mem q.1.2) p.1.2)
        have hg : (p.1 : G) = q.1 := by
          rw [htt] at h1; exact mul_right_cancel h1
        exact Prod.ext (Subtype.ext hg) htt
    exact_mod_cast hcard
  calc (T.card : ℝ≥0∞) * μ U = ∑ t ∈ T, μ U := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = ∑ t ∈ T, ∑' γ : Λ, ∫⁻ x, (γ • (t • U)).indicator 1 x ∂ν := Finset.sum_congr rfl key
    _ = ∫⁻ x, ∑ t ∈ T, ∑' γ : Λ, (γ • (t • U)).indicator (1 : G → ℝ≥0∞) x ∂ν := by
      rw [lintegral_finset_sum']
      · refine Finset.sum_congr rfl fun t _ => ?_
        rw [lintegral_tsum]
        exact fun γ => ((measurable_one.indicator (hmeasA γ t))).aemeasurable
      · intro t _
        exact (Measurable.ennreal_tsum fun γ => measurable_one.indicator (hmeasA γ t)).aemeasurable
    _ ≤ ∫⁻ _x, (hfin.toFinset.card : ℝ≥0∞) ∂ν := lintegral_mono hpt
    _ = (hfin.toFinset.card : ℝ≥0∞) * μ (S ∩ D) := by
      rw [lintegral_const, hν, Measure.restrict_apply_univ]

end GlobalTheory.Packing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveLineToAbelianVarietyConstStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projectiveLine_to_abelianVariety_const : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∀ (f₀ f₁ : Sp (Polynomial k) ⟶ B.left), f₀ ≫ B.hom = spMap (algebraMap k (Polynomial k)) → f₁ ≫ B.hom = spMap (algebraMap k (Polynomial k)) → spMap (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))) ≫ f₀ = spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial k) : Localization.Away (Polynomial.X : Polynomial k))).toRingHom ≫ f₁ → ∀ a b : Polynomial k →ₐ[k] k, spMap a.toRingHom ≫ f₀ = spMap b.toRingHom ≫ f₀ := by
  first | exact @GlobalTheory.LineConst.projLine_map_const | exact GlobalTheory.LineConst.projLine_map_const | (intros; apply GlobalTheory.LineConst.projLine_map_const <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiMapFst
section
set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleGen

def psiMap {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (a₁ b₁ a₂ b₂ : ℤ) : A ⊗ A ⟶ A ⊗ A :=
  lift (fst A A ^ a₁ * snd A A ^ b₁) (fst A A ^ a₂ * snd A A ^ b₂)

theorem psiMap_fst {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (a₁ b₁ a₂ b₂ : ℤ) :
    psiMap A a₁ b₁ a₂ b₂ ≫ fst A A = fst A A ^ a₁ * snd A A ^ b₁ := lift_fst _ _

theorem psiMap_snd {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (a₁ b₁ a₂ b₂ : ℤ) :
    psiMap A a₁ b₁ a₂ b₂ ≫ snd A A = fst A A ^ a₂ * snd A A ^ b₂ := lift_snd _ _

end GlobalTheory.AmpleGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadsZero
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BdryUnit

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.AllWt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def SameVec (Y : Model Xo c (RingHom.id c.F)) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (u : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) (v : Sp (DualNumber S) ⟶ Y.t.G.left) : Prop :=
  ∃ w : Sp (DualNumber S) ⟶ Y.oF.t.G.left,
    IsTanAtG Y.oF.t (ptF y) w ∧ w ≫ Y.m0.toSABMap.φ = u ∧ w ≫ Y.m.φ = v

def Matches (Y : Model Xo c (RingHom.id c.F)) (V : (Xo.XF c).Opens) (τ : Psi H) {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) (a : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Framed Y V τ.1 S (algebraMap c.F S)) : Prop :=
  a.x = ptF y ≫ Y.jQ ∧
    (∀ i : Fin Dw.p, ∃ j : Fin (Dw.mult τ.1), (j : ℕ) = i ∧ SameVec Y y (y.u τ.1 j) (a.v i).left) ∧
    ∀ i : Fin Dw.q, ∃ j : Fin (Dw.mult (conjEmb τ.1)), (j : ℕ) = i ∧ SameVec Y y (y.u (conjEmb τ.1) j) (a.w i).left

def Reads (Y : Model Xo c (RingHom.id c.F)) (V : (Xo.XF c).Opens) (τ : Psi H)
    (sig : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Rule Y V τ.1) (f : Rul Xo c) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), GlobalTheory.FlatLine.Tested y →
    ∀ a : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Framed Y V τ.1 S (algebraMap c.F S), Matches Y V τ y a →
      evR Xo c f y = sig S (algebraMap c.F S) a

end GlobalTheory.BdryUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisationNonarchimedeanCompat
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.LevelLaw

theorem omega_level_vP : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.Char F → ∀ (i : Fin D.R.m) (t : T0) (k : GA D (Vc D i)), VStd D i → k ∈ GfC (Vc D i) → ∀ hk : fin (Vc D i) k ∈ levJ R i t, R.ωP i t (k, 1) (R.vP i t) = (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ ⟨fin (Vc D i) k, hk⟩ : ℂˣ) : ℂ)⁻¹ • R.vP i t := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F h i t k _ hf hk
  have hl : Formalism.IndefR.Lev.finE (Vc D i) k ∈ Formalism.L2.DIV.lev D.sp.cm (Vc D i).gram (R.βV i)
      (Formalism.IndefR.Lev.flag1L (R.datVt i t)) := hk
  have hκ : Formalism.IndefR.Lev.IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) 1 k := ⟨hf, hl.1, Subgroup.mem_bot.1 hl.2⟩
  have hκ' : Formalism.IndefR.Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) 1 1 :=
    ⟨Subgroup.one_mem _, by rw [map_one]; exact Subgroup.one_mem _, by rw [map_one]; exact Formalism.L2.DIV.rTup_one⟩
  refine (GlobalTheory.T.weilAction_liftPair_stepVector_invLevelChar R h.lev h.models.inf h.thP.ωP h.thP.vP i t 1 k 1 hκ hκ').trans ?_
  exact congrArg (fun z : ℂˣ => (z : ℂ)⁻¹ • R.vP i t)
    (Formalism.IndefR.Lev.levFn_flag1 (V := Vc D i) (β := R.βV i) (L := R.datVt i t) (Formalism.IndefR.Lev.finE (Vc D i) k)).symm

end GlobalTheory.AdTh.LevelLaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativelyAcyclicOfCechVanishingAllCovers
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
open scoped CategoryTheory.Obj

namespace GlobalTheory.AmpleGen

theorem isRelAcyclic_of_not_NV : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (P : LB A.left),
    (∀ j : ℕ, ¬ NV A P (j + 1)) → GlobalTheory.CxForm.IsRelAcyclic A.hom A.hom P := by
  intro K _ A _ P hP U _ κ _ _ W hW hWU n
  by_cases hU : U = ⊤
  · subst hU
    have hWU' : ⨆ i, W i = ⊤ := by rw [hWU]; simp
    by_contra h
    exact hP n ⟨κ, inferInstance, inferInstance, W, hW, hWU', h⟩
  · have hb : U = ⊥ := by
      refine eq_bot_iff.2 fun x hx => (hU (eq_top_iff.2 fun y _ => ?_)).elim
      have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
      rwa [Subsingleton.elim y x]
    subst hb
    refine HomologicalComplex.ExactAt.of_isZero ?_
    rw [GlobalTheory.AbLaw.cechLB_X, ModuleCat.isZero_iff_subsingleton]
    refine ⟨fun a b => funext fun s => ?_⟩
    refine GlobalTheory.AbLaw.SecOnR.ext_of_cover _ (I := PEmpty) (fun i => i.elim) (fun i => i.elim) ?_ fun i => i.elim
    obtain ⟨i, hi⟩ := Finset.card_pos.1 (by rw [s.2]; exact Nat.succ_pos _ : 0 < s.1.card)
    refine (biInf_le W hi).trans (((le_iSup W i).trans hWU.le).trans ?_)
    simp

end GlobalTheory.AmpleGen
end
end

