import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0166
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0470
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0469
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0334
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0460
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0383
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NumberFieldLatticeDeterminedByLocalLattices
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0105
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0045
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0272
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle0006
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0351
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0260
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0293
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0396
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0392
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0466
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0465
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0222
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0365
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0086
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0058
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GoodOfHpEqOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
import Formalism.LocalRingCardinality.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountTypedOfVolumeStep
section
open Formalism.MainNotions.PlaceDegreeData

namespace GlobalTheory.CountBridge

theorem count_typed_of_volumeStep :
    GlobalTheory.FlagMeas.VolumeStep → ∀ A : ℝ, ∃ (n₀ : ℕ) (C₀ : ℝ), 0 ≤ C₀ ∧ ∀ n₁ ≥ n₀, ∀ C ≥ C₀,
      ∀ D : Formalism.BasicNotions.D7, Formalism.MainNotions.PlaceDegreeData.PointsLemma D n₁ A C (1 / 16) (1 / 16) := by
  intro hV A
  obtain ⟨n₀, C₀, hC₀, hcount⟩ := GlobalTheory.T.unitaryAutomorphicCounting_unbundled (GlobalTheory.T.unitaryAutomorphicCounting_of_compactDualVolumeRatio hV) A
  refine ⟨n₀, C₀, hC₀, fun n₁ hn₁ C hC _D => ?_⟩
  intro I b lam g g₀ e H _ _ _ σ w Hs _ _ _ σs tens μf _ fund R Re h hSet hData
  exact hcount n₁ hn₁ C hC I b lam g g₀ e H σ w Hs σs tens μf fund R Re h hSet hData

end GlobalTheory.CountBridge
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNormalisedLocalBesselDatumStatement
section
open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normalised_localBesselDatum : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), 1 ≤ k → IsSection k r L.z L.z' μsec → ∃ Bs : B.RealPlaceData k r L.Wp L.Wq, IsStdOf L μsec Bs := by
  first | exact @GlobalTheory.ThA.exists_isStdOf | exact GlobalTheory.ThA.exists_isStdOf | (intros; apply GlobalTheory.ThA.exists_isStdOf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsTermOfGlobalTermStrongApprox
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.TermSurj

section Places
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}

theorem ext_mul (A : Places F E sig) {n : ℕ} {p} {a b : (Fin n → E) ≃ₗ[E] (Fin n → E)} {a' b'}
    (ha : A.Ext p a a') (hb : A.Ext p b b') : A.Ext p (a * b) (a' * b') := by
  intro z
  show a' (b' (A.bc p z)) = A.bc p (a (b z))
  rw [hb, ha]

theorem ext_inv (A : Places F E sig) {n : ℕ} {p} {a : (Fin n → E) ≃ₗ[E] (Fin n → E)} {a'}
    (ha : A.Ext p a a') : A.Ext p a⁻¹ a'⁻¹ := by
  intro z
  have h := ha (a.symm z)
  rw [LinearEquiv.apply_symm_apply] at h
  change a'.symm (A.bc p z) = A.bc p (a.symm z)
  rw [← h, LinearEquiv.symm_apply_apply]

theorem eq_map_of_local (A : Places F E sig) {n : ℕ} {Λ Γ : Submodule (𝓞 E) (Fin n → E)}
    (hΛ : Submodule.IsLattice E Λ) (hΓ : Submodule.IsLattice E Γ) (x : (Fin n → E) ≃ₗ[E] (Fin n → E))
    (h : ∀ p, ∃ g, A.Ext p x g ∧ A.lat p Γ = g • A.lat p Λ) :
    Γ = Λ.map ((x : (Fin n → E) →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) := by
  ext y
  rw [(GlobalTheory.HL.PlacesRec.lattice_local A n Γ hΓ).1 y]
  constructor
  · intro hy
    refine ⟨x.symm y, ((GlobalTheory.HL.PlacesRec.lattice_local A n Λ hΛ).1 _).2 fun p => ?_, by simp⟩
    obtain ⟨g, hg, hp⟩ := h p
    have hy' := hy p
    rw [hp] at hy'
    obtain ⟨b, hb, hbe⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy'
    have e : g (A.bc p (x.symm y)) = A.bc p y := by rw [hg]; simp
    have hb' : b = A.bc p (x.symm y) := g.injective (by rw [e]; exact hbe)
    rw [← hb']
    exact hb
  · rintro ⟨z, hz, rfl⟩ p
    obtain ⟨g, hg, hp⟩ := h p
    rw [hp]
    have hz' := ((GlobalTheory.HL.PlacesRec.lattice_local A n Λ hΛ).1 z).1 hz p
    simp only [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
    rw [← hg z]
    exact Submodule.smul_mem_pointwise_smul _ g _ hz'

theorem term_eq_map {A : Places F E sig} {r k : ℕ} (G : GFrames A r k) (hk : 4 * r + 7 ≤ k) {d : G.Dat}
    {Λ Γ : G.Lt} (hΛ : G.IsTerm d Λ) (hΓ : G.IsTerm d Γ) :
    (∃ x ∈ G.N, Γ = Λ.map ((x : G.V →ₗ[E] G.V).restrictScalars (𝓞 E))) ∧
      ∃ x ∈ G.N', Γ = Λ.map ((x : G.V →ₗ[E] G.V).restrictScalars (𝓞 E)) := by
  obtain ⟨⟨n0, hn0, n0', hn0', h0⟩, -⟩ := GlobalTheory.T.globalHermitianFrames_rational_witnesses_phase A r k G hk d Λ hΛ
  obtain ⟨⟨n1, hn1, n1', hn1', h1⟩, -⟩ := GlobalTheory.T.globalHermitianFrames_rational_witnesses_phase A r k G hk d Γ hΓ
  refine ⟨⟨n1 * n0⁻¹, G.N.mul_mem hn1 (G.N.inv_mem hn0), eq_map_of_local A hΛ.1 hΓ.1 _ fun p => ?_⟩,
    ⟨n1' * n0'⁻¹, G.N'.mul_mem hn1' (G.N'.inv_mem hn0'), eq_map_of_local A hΛ.1 hΓ.1 _ fun p => ?_⟩⟩
  · obtain ⟨m0, -, e0⟩ := hn0 p
    obtain ⟨m0', -, e0'⟩ := hn0' p
    obtain ⟨m1, -, e1⟩ := hn1 p
    obtain ⟨m1', -, e1'⟩ := hn1' p
    obtain ⟨-, -, -, -, s0, -, -, -⟩ := h0 p m0 m0' e0 e0'
    obtain ⟨-, -, -, -, s1, -, -, -⟩ := h1 p m1 m1' e1 e1'
    refine ⟨m1 * m0⁻¹, ext_mul A e1 (ext_inv A e0), ?_⟩
    rw [s0, s1, smul_smul, inv_mul_cancel_right]
  · obtain ⟨m0, -, e0⟩ := hn0 p
    obtain ⟨m0', -, e0'⟩ := hn0' p
    obtain ⟨m1, -, e1⟩ := hn1 p
    obtain ⟨m1', -, e1'⟩ := hn1' p
    obtain ⟨-, -, -, -, -, s0, -, -⟩ := h0 p m0 m0' e0 e0'
    obtain ⟨-, -, -, -, -, s1, -, -⟩ := h1 p m1 m1' e1 e1'
    refine ⟨m1' * m0'⁻¹, ext_mul A e1' (ext_inv A e0'), ?_⟩
    rw [s0, s1, smul_smul, inv_mul_cancel_right]

end Places

section Glob
variable {D : D7}

theorem nlam_one' {T : D.host.E} (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F : LFlag (VS D) D.R.rS T) :
    (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ NLam Λ F := by
  refine ⟨⟨(Formalism.HermitianLatticesTheory.isom _).one_mem, ?_⟩, fun j x _ => by simp, fun x _ => by simp⟩
  ext x
  simp [Formalism.HermitianLatticesTheory.gmap]

theorem nlam_mul' {T : D.host.E} {Λ : Submodule (𝓞 D.host.E) (VS D).V} {F : LFlag (VS D) D.R.rS T}
    {a b : (VS D).V ≃ₗ[D.host.E] (VS D).V} (ha : a ∈ NLam Λ F) (hb : b ∈ NLam Λ F) : a * b ∈ NLam Λ F :=
  Formalism.MainNotions.BridgeLemma₂.c3eqv_NLam_trans hb ha

theorem nlam_inv' {T : D.host.E} {Λ : Submodule (𝓞 D.host.E) (VS D).V} {F : LFlag (VS D) D.R.rS T}
    {a : (VS D).V ≃ₗ[D.host.E] (VS D).V} (ha : a ∈ NLam Λ F) : a⁻¹ ∈ NLam Λ F :=
  Formalism.MainNotions.BridgeLemma₂.c3eqv_NLam_symm ha

theorem nlam_rat {T : D.host.E} {Λ : Submodule (𝓞 D.host.E) (VS D).V} {F : LFlag (VS D) D.R.rS T}
    {a : (VS D).V ≃ₗ[D.host.E] (VS D).V} (ha : a ∈ NLam Λ F) : a ∈ NRat F :=
  ⟨ha.1.1, ha.2.1, ha.2.2⟩

theorem rel_of_eqv {X : HidaSetting D} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)} {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V}
    {q p : GCar X u u' F0 F0' Λ Λ'} (h : Relation.EqvGen (GRel X u u' F0 F0' Λ Λ') q p) :
    ∃ a ∈ NLam Λ (lf D F0), ∃ b ∈ NLam Λ' (lf D F0'), q.1.2 = a * p.1.2 * b := by
  induction h with
  | rel x y hxy =>
    obtain ⟨n, hn, n', hn', e⟩ := hxy
    refine ⟨n⁻¹, nlam_inv' hn, n'⁻¹, nlam_inv' hn', ?_⟩
    rw [e]; group
  | refl x => exact ⟨1, nlam_one' _ _, 1, nlam_one' _ _, by group⟩
  | symm x y _ ih =>
    obtain ⟨a, ha, b, hb, e⟩ := ih
    refine ⟨a⁻¹, nlam_inv' ha, b⁻¹, nlam_inv' hb, ?_⟩
    rw [e]; group
  | trans x y z _ _ ih1 ih2 =>
    obtain ⟨a, ha, b, hb, e1⟩ := ih1
    obtain ⟨a', ha', b', hb', e2⟩ := ih2
    refine ⟨a * a', nlam_mul' ha ha', b' * b, nlam_mul' hb' hb, ?_⟩
    rw [e1, e2]; group

variable {Z : LocDat D} {T T' : D.host.E} {F0 : LFlag (VS D) D.R.rS T} {F0' : LFlag (VS D) D.R.rS T'}
  {FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS} {G : GFrames (placesOf Z) D.R.rS D.R.k}

theorem grp_mul (c : GCoord Z F0 F0' FP G) (σ a b : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
    c.grp σ (a * b) = c.grp σ a * c.grp σ b := by
  ext x : 1
  simp [GCoord.grp]

theorem grp_one (c : GCoord Z F0 F0' FP G) (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
    c.grp σ 1 = 1 := by
  ext x : 1
  simp [GCoord.grp]

theorem grp_inv (c : GCoord Z F0 F0' FP G) (σ a : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
    c.grp σ a⁻¹ = (c.grp σ a)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← grp_mul, inv_mul_cancel, grp_one])

theorem lat_gmap' (c : GCoord Z F0 F0' FP G) (σ τ : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) : c.lat σ (Formalism.HermitianLatticesTheory.gmap τ Λ) = c.lat (σ * τ) Λ := by
  unfold GCoord.lat Formalism.HermitianLatticesTheory.gmap
  rw [← Submodule.map_comp]
  rfl

theorem lat_inj (c : GCoord Z F0 F0' FP G) (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
    Function.Injective (c.lat σ) := by
  intro Λ₁ Λ₂ h
  unfold GCoord.lat at h
  exact Submodule.map_injective_of_injective
    (f := (((σ.trans c.e : (VS D).V ≃ₗ[D.host.E] G.V) : (VS D).V →ₗ[D.host.E] G.V).restrictScalars (𝓞 D.host.E)))
    (fun a b hab => (σ.trans c.e).injective hab) h

end Glob

end GlobalTheory.HL.TermSurj

namespace GlobalTheory.HL.TermSurj

theorem exists_term_of_global : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ Γ, G.IsTerm (G.datOf (c.lat ρ t₀.lam)) Γ → ∃ (t : TauC Y u u') (n m : ((VS D).V ≃ₗ[D.host.E] (VS D).V)), (Y.tO u u').rowOf t = (Y.tO u u').rowOf t₀ ∧ (n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m) ∧ Γ = c.lat (ρ * n) t.lam := by
  intro D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv Γ hΓ
  obtain ⟨hNiff, hN'iff, hlat, hsurj, -, -⟩ :=
    GlobalTheory.T.rational_unipotent_groups_lattices_global_coordinates D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv
  have hT0 := (GlobalTheory.T.movedTermLattice_isGlobalTerm_phase D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv).1
  have ht0 : Formalism.HermitianLatticesTheory.gmap t₀.lin t₀.lam' = t₀.lam := t₀.rep.2.2.2.1
  have e3 : c.lat ρ t₀.lam = c.lat (ρ * t₀.lin) t₀.lam' := by rw [← ht0, lat_gmap']
  obtain ⟨⟨x, hx, hΓx⟩, ⟨x', hx', hΓx'⟩⟩ := term_eq_map G hk hT0 hΓ
  obtain ⟨n, rfl⟩ := hsurj ρ x
  obtain ⟨m, rfl⟩ := hsurj (ρ * t₀.lin) x'
  have hn : n ∈ NRat (lf D (X.Fu u)) := (hNiff n).2 hx
  have hm : m ∈ NRat (lf D (X.Fu u')) := (hN'iff m).2 hx'
  have hΓn : Γ = c.lat (ρ * n) t₀.lam := by rw [hlat, hΓx]
  have hΓm : Γ = c.lat (ρ * t₀.lin * m) t₀.lam' := by rw [hlat, hΓx', e3]
  have hγmap : Formalism.HermitianLatticesTheory.gmap (n⁻¹ * t₀.lin * m) t₀.lam' = t₀.lam := by
    apply lat_inj c (ρ * n)
    rw [lat_gmap', ← hΓn, hΓm]
    congr 1
    group
  have hγiso : n⁻¹ * t₀.lin * m ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
    (Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).inv_mem hn.1) t₀.rep.2.2.1) hm.1
  have hPD := GlobalTheory.T.exists_admissible_integralFrame_of_localTerms D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv n m hn hm hγmap
    ⟨_, hΓn ▸ hΓ⟩
  obtain ⟨xp, hxp, -⟩ := (GlobalTheory.RatIsomPoint.ratLink_points D X).1 _ hγiso
  let p : GCar X u u' (X.Fu u) (X.Fu u') t₀.lam t₀.lam' := ⟨(xp, n⁻¹ * t₀.lin * m), hxp, hγiso, hγmap, hPD⟩
  let t : TauC Y u u' := ⟨t₀.lam, t₀.mem, t₀.lam', t₀.mem', Quot.mk _ p⟩
  have hq : Relation.EqvGen (GRel X u u' (X.Fu u) (X.Fu u') t₀.lam t₀.lam') (Quot.out (Quot.mk _ p)) p :=
    Quot.eqvGen_exact (Quot.out_eq _)
  obtain ⟨a, ha, b, hb, hab⟩ := rel_of_eqv hq
  have hlin : t.lin = (n * a⁻¹)⁻¹ * t₀.lin * (m * b) := by
    show (Quot.out (Quot.mk _ p)).1.2 = _
    rw [hab]
    show a * (n⁻¹ * t₀.lin * m) * b = _
    group
  have hn₂ : n * a⁻¹ ∈ NRat (lf D (X.Fu u)) := by
    refine (hNiff _).2 ?_
    rw [grp_mul, grp_inv]
    exact G.N.mul_mem hx (G.N.inv_mem ((hNiff a).1 (nlam_rat ha)))
  have hm₂ : m * b ∈ NRat (lf D (X.Fu u')) := by
    refine (hN'iff _).2 ?_
    rw [grp_mul]
    exact G.N'.mul_mem hx' ((hN'iff b).1 (nlam_rat hb))
  have hΓ₂ : Γ = c.lat (ρ * (n * a⁻¹)) t.lam := by
    show Γ = c.lat (ρ * (n * a⁻¹)) t₀.lam
    rw [← mul_assoc, ← lat_gmap', (nlam_inv' ha).1.2, hΓn]
  have hrow := (GlobalTheory.T.termRow_eq_iff_movedLatticeInnerData_eq D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv t (n * a⁻¹) (m * b)
    rfl rfl ⟨hn₂, hm₂, hlin⟩).2 (by
      rw [← hΓ₂]
      funext p
      haveI := ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).lf
      haveI := ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).char0
      exact (GlobalTheory.HL.DatumOf.datOf_term (G.S p) (hΓ.2 p)).symm)
  exact ⟨t, n * a⁻¹, m * b, hrow, ⟨hn₂, hm₂, hlin⟩, hΓ₂⟩

end GlobalTheory.HL.TermSurj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericIffZeroDefectGroupCoordinates
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.GenCoord

theorem generic_iff_locU {D : D7} (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (Z : LocDat D)
    (t₀ : TauC Y u u') : t₀.generic ↔
      ∀ p, ¬ LocNG.BBne (H := locH Z p) (locU Z p t₀.lam (lf D (X.Fu u)) t₀.frame (Tu D u) (Tu D u')) := by
  have hrows := Y.rowsOK u
  have hBF := Formalism.L2.SG.Pf.big_block_function_holds D u u'
  have hT := Formalism.L2.SG.Pf.bbTie_holds D Z
  have hMI : ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
      (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)), Formalism.L2.SG.Saturated.MplusIndep Λ (lf D F0) (gS D) F' :=
    fun F0 Λ F' => Formalism.L2.SG.Pf.m_plus_independent _ _ _ _
  have hg := genIffLocBB_of Z hT u u' hBF hMI (X.Fu u) (Y.what₂ u) hrows t₀.toTerm
  show t₀.toTerm.generic ↔ _
  rw [hg]
  refine forall_congr' fun p => not_congr ?_
  have hL := hrows.1 t₀.lam t₀.mem
  refine ((termBBne_iff_loc Z hT hrows hBF (hMI (X.Fu u)) t₀.toTerm p).symm.trans ?_).trans
    (GlobalTheory.T.signedLocalTerm_defect_iff_unsignedLocalTerm Z p t₀.lam (lf D (X.Fu u)) t₀.frame (Tu D u) (Tu D u'))
  refine Iff.trans ?_ (hT u u' (X.Fu u) t₀.lam t₀.frame hL t₀.rep.2.2.2.2 (hMI _ _ _) p)
  constructor
  · rintro ⟨F', ⟨h, hm⟩, P, hP, hbb⟩
    refine ⟨P, hP, ?_⟩
    have e := Formalism.L2.SG.TermDef.const_of_mk
      (fun y : Formalism.L2.SG.TermDef.Carrier (Formalism.L2.SG.TermDef.PD D t₀.lam (lf D (X.Fu u)) u') =>
        Formalism.L2.SG.Saturated.BBneP t₀.lam (gS D) (lf D (X.Fu u)) y.1 P)
      (fun a b hab => propext (hBF (X.Fu u) t₀.lam hL P a b hab)) hm
    exact e ▸ hbb
  · intro h
    exact ⟨t₀.frame, ⟨t₀.rep.2.2.2.2, rfl⟩, h⟩

theorem generic_iff_gen : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → (t₀.generic ↔ G.Gen (G.datOf (c.lat ρ t₀.lam)) (c.lat ρ t₀.lam)) := by
  intro D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv
  have hρ : ρ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hMv.1
  rw [generic_iff_locU X Y u u' (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) t₀]
  refine forall_congr' fun p => ?_
  obtain ⟨g, hgExt, hgU, -, -, -⟩ := GlobalTheory.T.rational_isometry_extends_local_isometry D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p ρ hρ
  have hGv : Gval (lf D (X.Fu u)) t₀.frame ≠ 0 := fun h => hG ((GlobalTheory.T.gramInvariant_isometry_unitriangular_moves F00 F'0 _ _ ρ U U' hMv).symm.trans h)
  have hRL : IsRowLat D (X.Fu u) t₀.lam := (Y.rowsOK u).1 t₀.lam t₀.mem
  obtain ⟨hIT, hTri'⟩ := GlobalTheory.LocOver.locU_isTerm D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) u u' (X.Fu u) t₀.lam hRL
    t₀.frame t₀.rep.2.2.2.2 hGv p
  have hOK : (Y.M p).OK := (Y.agree p).1
  have htIT := GlobalTheory.T.localTerm_move_unitary_isTerm (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) g hgU _ hIT
  obtain ⟨hTA, hTB⟩ := GlobalTheory.T.localFrames_movedTerm_unitriangular_change (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 _ _ ρ U U' g _ hMv hgExt hTri'
  obtain ⟨hA1, hA2, hA3, hA4⟩ := (hAt p).1
  rw [← hA1] at hTA
  rw [← hA2] at hTB
  obtain ⟨d, hd⟩ := GlobalTheory.T.exists_datum_of_two_congruent_frames (Y.M p) hOK (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS (FP p)
    (move g (locU (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p t₀.lam (lf D (X.Fu u)) t₀.frame (Tu D u) (Tu D u')))
    htIT hA3.symm hA4.symm hTA hTB
  have hW := ((GlobalTheory.T.terms_orbits_heights_amplitudes_in_coordinates (Y.M p) hOK (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS D.R.k (FP p) (G.S p)
    (c.c p)).1 d _ hd)
  have hlat := (GlobalTheory.T.rational_unipotent_groups_lattices_global_coordinates D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv).2.2.2.2.1 ρ hρ p g t₀.lam hgExt
  haveI := ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).lf
  haveI := ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).char0
  have hlat' : (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat p (c.lat ρ t₀.lam) = (c.c p).lat
      (move g (locU (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p t₀.lam (lf D (X.Fu u)) t₀.frame (Tu D u) (Tu D u'))).abelian₂ := hlat
  have hdat := GlobalTheory.HL.DatumOf.datOf_term (G.S p) hW.1
  show _ ↔ (G.S p).BBzero ((G.S p).datOf ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat p (c.lat ρ t₀.lam)))
    ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat p (c.lat ρ t₀.lam))
  rw [hlat', ← hdat, ← GlobalTheory.T.localTermDefect_ne_iff_move_linearEquiv (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) g, hW.2.2]
  exact not_not

end GlobalTheory.HL.GenCoord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalAmplitudeEqLocalAmplitudes
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.AmpLoc

set_option maxHeartbeats 1000000 in

theorem global_amp_local : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (R : ∀ p, LocNG.Reps (FP p)) (S1 : Finset (PlF D)) (Om : Finset {p // p ∈ S1}) (d : ∀ p : {p // p ∈ S1}, LocNG.Datum (FP p.1)), (∀ p, p ∉ S1 → (FP p).PrimeTo) → (∀ p, p ∈ Om ↔ ¬ (FP p.1).PrimeTo) → (∀ p : {p // p ∈ S1}, Over (FP p.1) (d p) (locU (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p.1 t₀.toTerm.lam (lf D (X.Fu u)) (Quot.out t₀.toTerm.cls).1 (Tu D u) (Tu D u'))) → ∀ Q : Prop → Prop, ‖G.amp (G.datOf (c.lat ρ t₀.lam)) (fun Γ => Q (¬ G.Gen (G.datOf (c.lat ρ t₀.lam)) Γ))‖ = ‖∑ A ∈ Om.powerset.filter (fun A => Q A.Nonempty), ∏ p, (if p ∈ A then LocNG.amp (R p.1) (d p) (LocNG.BBne (H := locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p.1)) else LocNG.amp (R p.1) (d p) (fun t => ¬ LocNG.BBne (H := locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p.1) t))‖ := by
  intro D X Y u u' hst hk w F00 F'0 FP hw hG hbase G c t₀ ρ U U' hmv R S1 Om d hout hOm hover Q
  have hT : G.IsTerm (G.datOf (c.lat ρ t₀.lam)) (c.lat ρ t₀.lam) :=
    (GlobalTheory.T.movedTermLattice_isGlobalTerm_phase D X Y u u' hst hk w F00 F'0 FP hw hG hbase G c t₀ ρ U U' hmv).1
  have hW := fun p => GlobalTheory.T.terms_orbits_heights_amplitudes_in_coordinates (Y.M p) (Y.agree p).1 (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p)
    D.R.rS D.R.k (FP p) (G.S p) (c.c p)
  obtain ⟨-, -, -, -, hgood⟩ := GlobalTheory.HL.BadPlaces.bad_places _ _ _ G hk _ _ hT
  have hOmS : G.Om ⊆ (S1 : Set (PlF D)) := by
    intro p hp
    by_contra hn
    exact hp ((hW p).2.2.2.1 (hout p hn))
  obtain ⟨κ, hκ, hdec⟩ := GlobalTheory.T.amplitude_expansion_over_finite_places _ _ _ G hk _ ⟨_, hT⟩ S1 hOmS
  rw [hdec Q, norm_mul, hκ, one_mul]

  have hloc : ∀ p : {p // p ∈ S1},
      (G.S p.1).amp (G.datOf (c.lat ρ t₀.lam) p.1)
          (fun Λ => ¬ (G.S p.1).BBzero (G.datOf (c.lat ρ t₀.lam) p.1) Λ) =
        LocNG.amp (R p.1) (d p) (LocNG.BBne (H := locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p.1)) ∧
      (G.S p.1).amp (G.datOf (c.lat ρ t₀.lam) p.1) ((G.S p.1).BBzero (G.datOf (c.lat ρ t₀.lam) p.1)) =
        LocNG.amp (R p.1) (d p) (fun t => ¬ LocNG.BBne (H := locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p.1) t) := by
    intro p
    haveI := ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p.1).lf
    haveI := ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p.1).char0
    have hu : (Function.update (G.datOf (c.lat ρ t₀.lam)) p.1 ((c.c p.1).dat (d p))) p.1 = (c.c p.1).dat (d p) :=
      Function.update_self _ _ _
    obtain ⟨h, hh, hδ⟩ := GlobalTheory.T.localDatum_of_term_in_movedLattice_orbit D X Y u u' hst hk w F00 F'0 FP hw hG hbase G c t₀ ρ U U' hmv p.1 (d p)
      (hover p) _ hu
    rw [hu] at hδ
    obtain ⟨e1, e2⟩ := (hW p.1).2.2.2.2 (R p.1) (d p)
    rw [e1, e2, ← hδ]
    constructor
    · refine (GlobalTheory.InvH.amp_mass_smul _ _ _ _ h hh _ _ _ ?_ ?_).1
      · intro s hs Λ hΛ hq hb
        exact hq ((GlobalTheory.FrameAct.stabiliser_acts_on_terms _ _ _ _ _ Λ hΛ s hs).2.2.2.2.2.2.2.1.1 hb)
      · intro Λ hΛ
        obtain ⟨-, -, -, hM, hs, -⟩ := GlobalTheory.HL.ComplAct.main _ _ _ _ _ Λ hΛ h hh
        exact not_congr ⟨fun e => hM.trans (e.trans hs.symm), fun e => hM.symm.trans (e.trans hs)⟩
    · refine (GlobalTheory.InvH.amp_mass_smul _ _ _ _ h hh _ _ _ ?_ ?_).1
      · intro s hs Λ hΛ hq
        exact (GlobalTheory.FrameAct.stabiliser_acts_on_terms _ _ _ _ _ Λ hΛ s hs).2.2.2.2.2.2.2.1.2 hq
      · intro Λ hΛ
        obtain ⟨-, -, -, hM, hs, -⟩ := GlobalTheory.HL.ComplAct.main _ _ _ _ _ Λ hΛ h hh
        exact ⟨fun e => hM.trans (e.trans hs.symm), fun e => hM.symm.trans (e.trans hs)⟩
  have hzero : ∀ p ∈ S1, (FP p).PrimeTo →
      (G.S p).amp (G.datOf (c.lat ρ t₀.lam) p) (fun Λ => ¬ (G.S p).BBzero (G.datOf (c.lat ρ t₀.lam) p) Λ) = 0 := by
    intro p _ hp
    have hBB := (hgood p (fun hm => hm ((hW p).2.2.2.1 hp))).1
    unfold Frames.amp
    exact (tsum_congr fun o => if_neg fun hh => hh.2 (hBB _ _ hh.1)).trans tsum_zero
  congr 1
  symm
  let emb : {p // p ∈ S1} ↪ PlF D := Function.Embedding.subtype _
  let embF : Finset {p // p ∈ S1} ↪ Finset (PlF D) := ⟨fun A => A.map emb, Finset.map_injective emb⟩
  calc _ = ∑ A ∈ Om.powerset.filter (fun A => Q A.Nonempty), ∏ p ∈ S1,
          (if p ∈ A.map emb then (G.S p).amp (G.datOf (c.lat ρ t₀.lam) p)
              (fun Λ => ¬ (G.S p).BBzero (G.datOf (c.lat ρ t₀.lam) p) Λ)
            else (G.S p).amp (G.datOf (c.lat ρ t₀.lam) p) ((G.S p).BBzero (G.datOf (c.lat ρ t₀.lam) p))) := by
        refine Finset.sum_congr rfl fun A _ => ?_
        rw [← Finset.prod_coe_sort S1]
        refine Finset.prod_congr rfl fun p _ => ?_
        have hm : (p.1 ∈ A.map emb) ↔ p ∈ A := Finset.mem_map' emb
        by_cases hp : p ∈ A
        · rw [if_pos hp, if_pos (hm.2 hp), (hloc p).1]
        · rw [if_neg hp, if_neg (fun h => hp (hm.1 h)), (hloc p).2]
    _ = ∑ B ∈ (Om.powerset.filter (fun A => Q A.Nonempty)).map embF, ∏ p ∈ S1,
          (if p ∈ B then (G.S p).amp (G.datOf (c.lat ρ t₀.lam) p)
              (fun Λ => ¬ (G.S p).BBzero (G.datOf (c.lat ρ t₀.lam) p) Λ)
            else (G.S p).amp (G.datOf (c.lat ρ t₀.lam) p) ((G.S p).BBzero (G.datOf (c.lat ρ t₀.lam) p))) :=
        by rw [Finset.sum_map]; rfl
    _ = _ := by
        apply Finset.sum_subset
        · intro B hB
          obtain ⟨A, hA, rfl⟩ := Finset.mem_map.1 hB
          rw [Finset.mem_filter, Finset.mem_powerset] at hA ⊢
          refine ⟨fun x hx => ?_, ?_⟩
          · obtain ⟨y, -, rfl⟩ := Finset.mem_map.1 hx
            exact y.2
          · show Q (A.map emb).Nonempty
            rw [Finset.map_nonempty]
            exact hA.2
        · intro B hB hn
          rw [Finset.mem_filter, Finset.mem_powerset] at hB
          by_cases hall : ∀ p ∈ B, ¬ (FP p).PrimeTo
          · exfalso
            apply hn
            have e : (B.subtype (· ∈ S1)).map emb = B := Finset.subtype_map_of_mem hB.1
            refine Finset.mem_map.2 ⟨B.subtype (· ∈ S1), ?_, e⟩
            rw [Finset.mem_filter, Finset.mem_powerset]
            refine ⟨fun q hq => (hOm q).2 (hall q.1 (Finset.mem_subtype.1 hq)), ?_⟩
            rw [← Finset.map_nonempty (f := emb), e]
            exact hB.2
          · push_neg at hall
            obtain ⟨p, hpB, hp⟩ := hall
            exact Finset.prod_eq_zero (hB.1 hpB) (by rw [if_pos hpB]; exact hzero p (hB.1 hpB) hp)

end GlobalTheory.HL.AmpLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalDataOfTermLatticeAndOrbitsStatement
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localData_of_term_lattice_and_orbits : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (t : TauC Y u u') (Λ : LV D), TG F F' t Λ → ∃ y : Dat Z FP, LocOver Λ y ∧ ∀ p d, GlobalTheory.LocOver.Over (FP p) d (GlobalTheory.LocOver.locU Z p t.toTerm.lam (lf D (X.Fu u)) (Quot.out t.toTerm.cls).1 (Tu D u) (Tu D u')) ↔ LocNG.Datum.Rel d (y p) := by
  first | exact @GlobalTheory.Unfold.TermLocal.local_data_of_term | exact GlobalTheory.Unfold.TermLocal.local_data_of_term | (intros; apply GlobalTheory.Unfold.TermLocal.local_data_of_term <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantLengthMomentsAmplitudesLargeGapStatement
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.majorantLength_moments_amplitudes_largeGap : GlobalTheory.GapIn.Hyp → ∀ Cg cb Cu cT CT C0 C1 Cq : ℝ, ∃ C : ℝ, ∀ Cn : ℝ, ∃ m₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), 1000 ≤ Cl → Big D large₂ Cl m₀ → MomIn D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 Cq C := by
  first | exact @GlobalTheory.AmpMomentsGap.amplitude_moments_gap | exact GlobalTheory.AmpMomentsGap.amplitude_moments_gap | (intros; apply GlobalTheory.AmpMomentsGap.amplitude_moments_gap <;> assumption)
end

