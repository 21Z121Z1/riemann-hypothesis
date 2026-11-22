import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0283
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1094
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0255
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1394
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1149
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1525
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0231
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0245
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0181
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1065
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0976
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0075
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsFundamentalDomainOfHaar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0427
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0409
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0425
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0299

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrtWLeHPart
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3

set_option maxHeartbeats 1000000 in

theorem prtW_le_hPart : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → ∀ (π : D.what₂.FT) c p, HasEig R F Y π c → R.Carries p c → ∀ i : Fin D.R.m, (Y.IL.prtW : ∀ i : Fin D.R.m, D.what₂.FT → Submodule ℂ (AmbT (R.MW i (sg0 D A3.A)))) i π ≤ (hPart (R.MW i (sg0 D A3.A)) (levG _ (R.βW i) (R.datWp i R.triv)) (A3.A.ok A3.A.μ0) R.pl A3.A.q (RealDat.polW (A := A3.A) p.1.1)).map (PiTensorProduct.lift : Mult.MMap (R.MW i (sg0 D A3.A)) ≃ₗ[ℂ] _).toLinearMap := by
  intro _ _ _ hcusp D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH _ π c p hc hcar i
  obtain ⟨hC, -, -, -⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hP.char hH.aux.ex
  have ht : Y.tupT D.what₂.mu0 = A3.A.μ0 := by rw [← Y.tup0, Y.tupT_tup]
  have hQ : R.Q A3.A.μ0 = ∅ := (GlobalTheory.GoodPrimes.good_primes R.toRealDat F.lv2 hC.lev).1
  have hSb : R.Sb = R.Pg := hP.char.allPl
  have hSF : GlobalTheory.Hk3.IsSF R.toRealDat (SsetF R.toRealDat (Y.tupT D.what₂.mu0)) := by
    classical
    intro v
    unfold SsetF
    rw [ht, hQ, hSb, Finset.union_empty, Finset.mem_image]
    refine exists_congr fun PP => and_congr_right fun _ => ?_
    rw [← underPl_asIdeal]
    exact ⟨fun h => by rw [h], fun h => HeightOneSpectrum.ext h⟩
  have hlab := GlobalTheory.T.heckePolynomials_of_carried_eigensystem R F (GlobalTheory.Chain.LiftConv.liftInteg_of_cuspRapidDecay hcusp D) hH.ok hP.char hH.aux.ex
    (GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hcusp R.toRealDat)
    (GlobalTheory.AdjPart.adjoint_injective_on_part R ⟨hH.prim.posScal.1, fun i t p => hH.prim.posScal.2 i t p _⟩ hH.prim.thmB)
    p c hcar
  rw [Y.prtWE i π]
  refine Submodule.map_mono fun U hU => ?_
  obtain ⟨x, hx, rfl⟩ := GlobalTheory.T.typePart_le_eigensystemPart_principalLevel R.toRealDat F.lv2 hH.ok.ok2 hC _ hSF Y.hF Y.PY Y.PW Y.stdPsi.1 Y.stdPsi.2
    _ ⟨0, Y.hm⟩ c hc i U hU
  exact (GlobalTheory.T.full_algebra_part_le_split_hecke_part R.toRealDat F.lv2 hH.ok.ok2 hC _ hSF c _).2 i (fun P hP => (hlab P hP).2) x hx

end GlobalTheory.Mem.R3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealPointMovesAdelicThetaByDetCharacter
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.RealMove

open GlobalTheory.IndefiniteRowSideFullHecke.VacuumCharacterDeterminant (detPos detNeg vacChar)
open scoped ComplexOrder

variable {D : D7} {S T : HSp D}

theorem root_eq {χ : (AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D χ n) (hn : Even n) {g : GA D T} {x x' : (AE D)ˣ}
    (hx : IsDetRoot T g x) (hx' : IsDetRoot T g x') : χ x' = χ x := by
  obtain ⟨a, rfl⟩ := (GlobalTheory.Member.isDetRoot_laws D T).2.1 g x x' hx hx'
  obtain ⟨⟨η, hη⟩, h2⟩ := h
  obtain ⟨m, rfl⟩ := hn
  rw [map_mul, h2 η hη a, pow_add, ← mul_pow, GlobalTheory.VolHeckeCompare.IsEta_mul_self hη, one_pow, mul_one]

theorem om_compact (C : GlobalTheory.Ker.Ctx S T) {χS χT η : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO C.ψ S T χS χT om) (hη : IsEtaTilde D η)
    {s : Fam T} (hs : ∀ τ, IsCartanInv (gramAt D T τ) (s τ)) {k : GA D T} (hk : k ∈ GinfC T)
    (hc : ∀ τ, s τ * compAt C.θ τ (Formalism.L2.Theta.mt T k) = compAt C.θ τ (Formalism.L2.Theta.mt T k) * s τ)
    {y : (AE D)ˣ} (hy : IsDetRoot T k y) {f : WO S T → ℂ} (hf : IsThetaFunO C.ψ S T f)
    (hv : ∀ τ, IsFockVacAt (heisO C.ψ S T) C.θ τ (cplxO 1 (s τ)) f) :
    om (1, k) f = (((χS y : Circle) : ℂ) * vacChar C.θ T s S.rank (fun _ => 0) k) • f := by
  have hdet : ∀ τ, (gramAt D T τ).det ≠ 0 := fun τ => by
    have := (hs τ).2.2.det_pos.ne'
    rw [Matrix.det_mul] at this
    exact left_ne_zero_of_mul this
  obtain ⟨y₀, hy₀, hv₀⟩ := GlobalTheory.OneMapRef.RealMove.exists_root C.inf T hdet k hk
  have hS : ∀ τ, IsCartanInv (gramAt D S τ) 1 := fun τ => by
    have e : gramAt D S τ = 1 := by
      unfold gramAt
      rw [C.m.gS]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    rw [e]
    exact ⟨one_mul _, by simp, by rw [one_mul]; exact Matrix.PosDef.one⟩
  have h1 : IsDetRoot S 1 1 := by simp [IsDetRoot]
  rw [GlobalTheory.T.weilDatum_realPlaces_fockVacuum_character D C.ψ hW.std S T C.θ C.inf χS χT om η hη hW (fun _ => 1) s hS hs 1 (one_mem _) k hk
    (fun τ => by rw [one_mul, mul_one]) hc 1 y₀ h1 hy₀ f hf hv, root_eq hW.resS C.even hy₀ hy]
  congr 1
  obtain ⟨m, hm⟩ := C.even
  have e1 := hv₀ (η * (η ^ (S.rank + 1))⁻¹) (fun _ => -(m : ℤ)) fun τ => by
    have := GlobalTheory.OneMapRef.RealMove.hasInfExp_twist (hη.2.2.2 τ) (hη.2.2.2 τ) (S.rank + 1)
    convert this using 1
    rw [hm]
    push_cast
    ring
  have e2 : ((χT * (η ^ T.rank)⁻¹) 1)⁻¹ * (χS * (η ^ S.rank)⁻¹) y₀ = χS y₀ * (η * (η ^ (S.rank + 1))⁻¹) y₀ := by
    simp only [map_one, inv_one, one_mul, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.pow_apply, pow_succ,
      mul_inv]
    rw [mul_left_comm (η y₀), mul_inv_cancel, mul_one]
  rw [e2, Circle.coe_mul, e1, mul_assoc, ← Finset.prod_mul_distrib, vacChar]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  obtain ⟨p, -, hd⟩ := GlobalTheory.OneMapRef.RealMove.detPlus_one (n := S.rank) (s τ) (hs τ).1
  obtain ⟨d1, d2⟩ := hd (compAt C.θ τ (Formalism.L2.Theta.mt S 1⁻¹)) (compAt C.θ τ (Formalism.L2.Theta.mt T k)) (hc τ)
  have e3 : (compAt C.θ τ (Formalism.L2.Theta.mt S 1⁻¹)).det = 1 := by
    rw [GlobalTheory.OneMapRef.RealMove.det_compAt, inv_one]
    unfold Formalism.L2.Theta.mt
    rw [map_one, Units.val_one, Matrix.det_one, map_one, map_one]
  have e4 : (compAt C.θ τ (Formalism.L2.Theta.mt T k)).det ≠ 0 := by
    intro h0
    have h2 := congrArg det (GlobalTheory.Ker.ONBasis.compAt_unitary C τ k)
    rw [det_mul, h0, mul_zero] at h2
    exact hdet τ h2.symm
  have hc' := hc τ
  rw [d1, e3]
  generalize compAt C.θ τ (Formalism.L2.Theta.mt T k) = b at *
  have p1 : detPos (s τ) b = ((1 / 2 : ℂ) • (1 + s τ) * b + (1 / 2 : ℂ) • (1 - s τ)).det := by
    rw [detPos, Matrix.mul_smul, Matrix.smul_mul, mul_add, add_mul, hc', one_mul, mul_one]
  have p2 : detNeg (s τ) b = ((1 / 2 : ℂ) • (1 - s τ) * b + (1 / 2 : ℂ) • (1 + s τ)).det := by
    rw [detNeg, detPos, Matrix.mul_smul, Matrix.smul_mul, ← sub_eq_add_neg, sub_neg_eq_add, mul_sub, sub_mul, hc',
      one_mul, mul_one]
  rw [← p1, ← p2] at d2
  rw [← p1, d2]
  rw [d2] at e4
  have h0 := left_ne_zero_of_mul e4
  have e5 : S.rank / 2 = m := by omega
  rw [e5, zero_add, zero_sub, _root_.zpow_neg, _root_.zpow_neg, zpow_natCast, zpow_natCast, zpow_natCast, hm,
    one_pow, mul_one, mul_pow, pow_add, mul_inv]
  have := pow_ne_zero m h0
  field_simp

theorem om_real (C : GlobalTheory.Ker.Ctx S T) {χS χT η : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO C.ψ S T χS χT om) (hη : IsEtaTilde D η)
    {a : GA D T} (ha : a ∈ GinfC T) {y : (AE D)ˣ} (hy : IsDetRoot T a y) {B : C.Bas} (hB : C.IsB B)
    {φ : TF S.rank C.g} (hφ : GlobalTheory.SW.IsSB φ) :
    om (1, a) (C.Th (C.xB B) φ) = ((χS y : Circle) : ℂ) • C.Th (C.xB (C.mvB a B)) φ := by
  obtain ⟨χ, -, χmul, hχ⟩ := GlobalTheory.FrameEquiv.exists_real_character D S T C om (GlobalTheory.Ker.isWeak_of_datum hW)
  have hJ := (GlobalTheory.Ker.onBasis_frame_period D S T C).2
  have hd := GlobalTheory.FrameEquiv.RealChar.xB_mem_dom C hB
  by_cases h0 : φ = 0
  · rw [hχ a ha B hB φ hφ, h0, GlobalTheory.FrameEquiv.RealChar.Th_zero C
      (GlobalTheory.FrameEquiv.RealChar.xB_mem_dom C ((hJ B hB).2.2.2.2.2 a).1), smul_zero, smul_zero]
  obtain ⟨hex, -, -, hmul⟩ := GlobalTheory.Member.isDetRoot_laws D T
  choose rt hrt using hex
  have hne : ∀ g, ((χS (rt g) : Circle) : ℂ) ≠ 0 := fun g => Circle.coe_ne_zero _
  have key := GlobalTheory.FrameEquiv.mulFun_eq_one_of_eq_one_on_maxCompact D T C.θ C.inf (C.sB B)
    (fun τ => ((hJ B hB).2.2.1 τ).1) (fun u => χ u / (χS (rt u) : Circle))
    (fun u hu u' hu' => by
      simp only [χmul u hu u' hu']
      rw [root_eq hW.resS C.even (hmul _ _ _ _ (hrt u) (hrt u')) (hrt (u * u')), map_mul, Circle.coe_mul,
        mul_div_mul_comm])
    (fun k hk hc => by
      have e1 := om_compact C hW hη (fun τ => ((hJ B hB).2.2.1 τ).1) hk (fun τ => (hc τ).symm) (hrt k)
        (GlobalTheory.Ker.ZakEx.isZak_Th D S T C _ hd φ hφ).1.1 ((GlobalTheory.Ker.fvec_Th_zero D S T C).2 B hB φ hφ).1
      have e2 := hχ k hk B hB φ hφ
      have e3 := GlobalTheory.FrameEquiv.CompactMove.Th_mvB D S T C B hB k hk hc φ hφ
      rw [← smul_smul, ← e3, e2] at e1
      have e4 := smul_left_injective ℂ (GlobalTheory.FrameEquiv.RealChar.Th_ne_zero C
        (GlobalTheory.FrameEquiv.RealChar.xB_mem_dom C ((hJ B hB).2.2.2.2.2 k).1) hφ h0) e1
      show χ k / (χS (rt k) : Circle) = 1
      rw [e4, div_self (hne k)]) a ha
  rw [hχ a ha B hB φ hφ, (div_eq_one_iff_eq (hne a)).1 key, root_eq hW.resS C.even hy (hrt a)]

set_option maxHeartbeats 1000000 in

theorem zak_om_real : ∀ (D : D7) (S T : HSp D) (r g : ℕ) (hr : T.rank = r) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (X : Data D.host.E r) (eT : D.what₂.Tau ≃ X.Ψ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (hS : IsSet ψ θ S T hr X eT bas), ∀ (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → (∃ η, IsEtaTilde D η) → ∀ Z : Fam T, IsONeg T X.p0 Z → ∀ a ∈ GinfC T, ∀ y : (AE D)ˣ, IsDetRoot T a y → ∀ φ : TF S.rank g, GlobalTheory.SW.IsSB φ → ∀ f, Zak ψ θ hr eT bas idx (frOf hr eT Z) φ f → Zak ψ θ hr eT bas idx (frOf hr eT (mvZ θ a Z)) (((χS y : Circle) : ℂ) • φ) (om (1, a) f) := by
  intro D S T r g hr ψ θ X eT bas idx hS χS χT om hW ⟨η, hη⟩ Z hZ a ha y hy φ hφ f hf
  obtain ⟨X', m, hq', bas', idx', hs, π, -, -, -, H⟩ := GlobalTheory.T.exists_conjugateModel_same_thetaFunctions D S T r g hr ψ θ X eT bas idx hS (r - X.p0)
    (Nat.add_sub_cancel' X.p0_le)
  set C := ctxOf hS.1 hS.2.1 hS.2.2.2.1 X' m hq' bas' idx' hs with hC
  have hB := (H Z).1.1 hZ
  have em : (fun ρ => (mvZ θ a Z ρ).submatrix id π) = C.mvB a fun ρ => (Z ρ).submatrix id π := by
    funext ρ
    ext i j
    rfl
  have hB' := (((GlobalTheory.Ker.onBasis_frame_period D S T C).2 _ hB).2.2.2.2.2 a).1
  have hZ' : IsONeg T X.p0 (mvZ θ a Z) := (H _).1.2 (em ▸ hB')
  have hd := GlobalTheory.FrameEquiv.RealChar.xB_mem_dom C hB
  have hd' := GlobalTheory.FrameEquiv.RealChar.xB_mem_dom C hB'
  have e1 := (GlobalTheory.Ker.ZakEx.isZak_Th D S T C _ hd φ hφ).2 f ((((H Z).2 hZ).2.1 φ f).2 hf)
  refine (((H _).2 hZ').2.1 _ _).1 ?_
  have hφ' : GlobalTheory.SW.IsSB (((χS y : Circle) : ℂ) • φ) := (isSB_algebra_haar_linear _ _ _ _ _ hφ hφ).2.1 _
  rw [em, e1, om_real C hW hη ha hy hB hφ, ← (GlobalTheory.Ker.Ctx.th_laws D S T C _ hd' φ hφ).2.1]
  exact (GlobalTheory.Ker.ZakEx.isZak_Th D S T C _ hd' _ hφ').1

end GlobalTheory.OneMapRef.RealMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideRationalLevelDataStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.side_rational_level_data : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → (∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → (tp.psi w).ValuesIn 0 D.what₂.embLL) → ∀ (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T), ∃ (Y : LocAut X) (Cb : LocBC Y), Nonempty (AutSpec A M tp.tup Sp.iq Y Cb) := by
  first | exact @GlobalTheory.AutPart.exists_autSpec | exact GlobalTheory.AutPart.exists_autSpec | (intros; apply GlobalTheory.AutPart.exists_autSpec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitHeckeOperatorInverseConjugatePlaceCosetSumStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitHeckeOperator_inverse_conjugatePlace_cosetSum : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L)
    (ϖ : s.v.adicCompletion (maximalRealSubfield L)), IsUnif L s.v ϖ → ∀ (k : ℕ), k ≤ n →
    ∀ (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* (GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L), Continuous i →
    ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) ((GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L)) V)
    (R : Finset (GAf L n)), (∀ γ ∈ R, γ ∈ tSet L n s ϖ k) → (∀ x ∈ tSet L n s ϖ k, ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ Umax L n) →
    ∀ e ∈ GlobalTheory.PRep.fixed ρ (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n),
      GlobalTheory.LFun.heckeVec ρ (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n)
                   (fun g => Formalism.UG.Tj ℂ n (Formalism.UG.Ov L (GlobalTheory.HeckeFrob.conjSplit s).w) (i ϖ) k g⁻¹) e =
        ∑ γ ∈ R, ρ (Matrix.GeneralLinearGroup.map i.toRingHom ((GlobalTheory.HeckeFrob.conjSplit s).loc n γ)) e := by
  first | exact @GlobalTheory.HeckeEigCoset.heckeVec_Tj_inv_conj_eq_sum | exact GlobalTheory.HeckeEigCoset.heckeVec_Tj_inv_conj_eq_sum | (intros; apply GlobalTheory.HeckeEigCoset.heckeVec_Tj_inv_conj_eq_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaKernelLieActionThroughWeylAlgebraStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKernel_lieAction_through_weylAlgebra : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), GlobalTheory.Ker.IsWeak ψ S T om → OmCont ψ S T om → ∀ θ : InfF D, IsInfFam θ → ∃ x d : D.what₂.Tau → Fin T.rank × Fin S.rank → Module.End ℂ (GlobalTheory.RealWeil.thetaSub ψ S T), ∀ τ, IsCCR (x τ) (d τ) ∧ (∀ X ∈ lieAt T τ, ∃ lam : ℂ, ∀ f g h, HasDerivAt (fun t : ℝ => thKer ψ S T om f g (h * oneP θ T τ X t)) (thKer ψ S T om ((∑ i, ∑ j, X i j • ∑ a, x τ (i, a) * d τ (j, a)) f + lam • f) g h) 0) ∧ ∀ Y ∈ lieAt S τ, ∃ lam : ℂ, ∀ f g h, HasDerivAt (fun t : ℝ => thKer ψ S T om f (g * oneP θ S τ Y t) h) (thKer ψ S T om ((∑ a, ∑ b, Y a b • -∑ i, x τ (i, b) * d τ (i, a)) f + lam • f) g h) 0 := by
  first | exact @GlobalTheory.Mem.Lift.WeylAction.weyl_action | exact GlobalTheory.Mem.Lift.WeylAction.weyl_action | (intros; apply GlobalTheory.Mem.Lift.WeylAction.weyl_action <;> assumption)
end

