import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0342
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0386
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0236
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0760
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0324
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0316
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0314
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0332
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0309
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0327
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0326
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0312
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0302
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0393
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0264
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0343
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0370
import Formalism.LocalToGlobal.Divisibility.QLocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0390
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0389
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelIndexLevelUnipotentCoprimePrime
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecomposition
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsLevel

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalReciprocityUnramifiedSpherical
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.SphLoc

section Alg
variable {G V X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]

theorem fixed_ne_bot_of_mem_iSup {ι : Type} [Finite ι] {σ : Representation ℂ G V} (hσ : σ.IsIrreducible)
    {ρ : Representation ℂ G X} (T : ι → σ.IntertwiningMap ρ) (K : Subgroup G) {f : X}
    (hf : f ∈ ⨆ j, LinearMap.range (T j).toLinearMap) (hf0 : f ≠ 0) (hK : ∀ k ∈ K, ρ k f = f) :
    GlobalTheory.PRep.fixed σ K ≠ ⊥ :=
  GlobalTheory.T.fixedVectors_ne_bot_of_mem_sum_intertwining_ranges hσ T K hf hf0 hK

end Alg

section Val
open ValuativeRel Filter Topology

variable {K K' : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field K'] [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']

theorem tendsto_pow_zero {x : K} (h : valuation K x < 1) : Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  rw [(IsValuativeTopology.hasBasis_nhds_zero' K).tendsto_right_iff]
  intro γ hγ
  have : MulArchimedean (ValueGroupWithZero K) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨n, hn⟩ := exists_pow_lt₀ h (Units.mk0 γ hγ)
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' h.le hm) hn

theorem lt_one_mem_nhds : {y : K' | valuation K' y < 1} ∈ 𝓝 (0 : K') := by
  refine (IsValuativeTopology.hasBasis_nhds_zero' K').mem_iff.2 ⟨1, one_ne_zero, fun y hy => hy⟩

theorem lt_one_of_map (i : K →+* K') (hi : Continuous i) {x : K} (h : valuation K x < 1) :
    valuation K' (i x) < 1 := by
  have h1 : Tendsto (fun n : ℕ => i x ^ n) atTop (𝓝 0) := by
    have := (hi.tendsto 0).comp (tendsto_pow_zero h)
    simpa [Function.comp_def, map_pow] using this
  obtain ⟨N, hN⟩ := (h1.eventually lt_one_mem_nhds).exists
  by_contra hc
  push Not at hc
  have : 1 ≤ valuation K' (i x ^ N) := by rw [map_pow]; exact one_le_pow₀ hc
  exact absurd hN (not_lt.2 this)

theorem le_one_of_map (i : K →+* K') (hi : Continuous i) {y : K} (h : valuation K' (i y) ≤ 1) :
    valuation K y ≤ 1 := by
  by_contra hc
  push Not at hc
  have hy : y ≠ 0 := fun h0 => by simp [h0] at hc
  have h1 : valuation K y⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hc
  have h2 := lt_one_of_map i hi h1
  rw [map_inv₀, map_inv₀] at h2
  have h0 : (0 : ValueGroupWithZero K') < valuation K' (i y) := by
    rw [zero_lt_iff, Valuation.ne_zero_iff]
    exact (map_ne_zero i).2 hy
  exact absurd h (not_le.2 ((inv_lt_one₀ h0).1 h2))

end Val

section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem mem_Umax_of_mem_KO (s : SplitPlace L)
    (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (hi : Continuous i) (x : GAf L n)
    (hx : TrivOutside {s.v} x)
    (hk : Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x) ∈ GlobalTheory.SplitWeil.KO (s.w.adicCompletion L) (Fin n)) :
    x ∈ Umax L n := by
  have key : ∀ y, ValuativeRel.valuation _ (i y) ≤ 1 → Valued.v y ≤ 1 := fun y hy =>
    (GlobalTheory.CuspRep.ParLaws.valuation_le_one_iff s.v y).1 (le_one_of_map i.toRingHom hi hy)
  rw [GlobalTheory.SplitFlip.mem_KO_iff] at hk
  refine GlobalTheory.TSetFin.mem_Umax_of_loc s x hx (fun a b => key _ (hk.1 a b)) (fun a b => key _ ?_)
  have h2 := hk.2 a b
  rw [← map_inv, ← map_inv] at h2
  exact h2

theorem isSpherical_of_sphAt (π : NG.AutRep L n) (s : SplitPlace L)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))) (hσ : IsLocS π.S s σ) (hs : π.SphAt s.v) :
    GlobalTheory.SmGL.IsSpherical σ.ρ := by
  classical
  obtain ⟨i, T₀, hi, hic, -, -, -⟩ := id hσ
  obtain ⟨f, hf, hf0, hfix⟩ := hs
  have hI := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s
  choose lift hlift using fun A => (hI.2.2 A).exists
  have huniq : ∀ A x, TrivOutside {s.v} x → s.loc n x = A → x = lift A := fun A x hx e =>
    (hI.2.2 A).unique ⟨hx, e⟩ (hlift A)
  have hmul : ∀ A B, lift (A * B) = lift A * lift B := fun A B =>
    (huniq _ _ (GlobalTheory.TSetFin.triv_mul (hlift A).1 (hlift B).1) (by rw [map_mul, (hlift A).2, (hlift B).2])).symm
  have htriv1 : TrivOutside {s.v} (1 : GAf L n) := by
    intro v _
    show ((1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) = 1
    rw [Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hone : lift 1 = 1 := (huniq _ _ htriv1 (map_one _)).symm
  let e : GL (Fin n) (s.w.adicCompletion L) →* GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) :=
    Matrix.GeneralLinearGroup.map i.symm.toRingHom
  have hloc : ∀ g, Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n (lift (e g))) = g := fun g => by
    rw [(hlift _).2]
    exact Units.ext (Matrix.ext fun a b => i.apply_symm_apply _)
  let ρX : Representation ℂ (GL (Fin n) (s.w.adicCompletion L)) (GAf L n → π.W) :=
    { toFun := fun g => NG.rt L n (lift (e g))
      map_one' := by
        simp only [map_one, hone]
        ext φ x
        simp [NG.rt]
      map_mul' := fun g h => by
        simp only [map_mul, hmul]
        ext φ x
        simp [NG.rt, mul_assoc] }
  have hiso : f ∈ NG.isoTyp π.ρ π.S := by
    unfold NG.isoTyp
    exact Submodule.mem_sSup_of_mem (show π.S ∈ {S' | NG.IsIrrRep π.ρ S' ∧ NG.IsoRep π.S S'} from
      ⟨π.irrS, LinearEquiv.refl ℂ _, fun _ _ _ e => e⟩) hf
  have h1 := GlobalTheory.T.isotypicPart_spanned_by_splitPlace_localComponent L n π.toAlgWt π.S π.irrS s σ hσ i hi hic hiso
  rw [iSup_subtype', Submodule.mem_iSup_iff_exists_finset] at h1
  obtain ⟨t, ht⟩ := h1
  rw [iSup_subtype'] at ht
  let Tm : {j // j ∈ t} → σ.ρ.IntertwiningMap ρX := fun j =>
    ⟨j.1.1, fun g => LinearMap.ext fun a => by
      have := j.1.2.2 (lift (e g)) (hlift _).1 a
      rw [hloc] at this
      exact this⟩
  refine fixed_ne_bot_of_mem_iSup σ.irr Tm (GlobalTheory.SplitWeil.KO _ (Fin n)) ht hf0 fun k hk => ?_
  show NG.rt L n (lift (e k)) f = f
  exact hfix _ (mem_Umax_of_mem_KO s i hi _ (hlift _).1 (by rw [hloc]; exact hk)) (hlift _).1

end

end GlobalTheory.SphLoc

end

section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.SphLoc.main : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (π : NG.AutRep D.host.E D.R.nV) (s : SplitPlace D.host.E) x,
    GlobalTheory.AutQuot.LocAt π s.w x → π.SphAt s.v → (GlobalTheory.CuspRep.ParLaws.locRec hL (D.nd.plOm.2 s.w) x).unr := by
  intro hL D π s x hx hs
  obtain ⟨s', σ, h, hσ, e⟩ := hx
  have hv : s'.v = s.v := HeightOneSpectrum.ext (by rw [← s'.w_under, ← s.w_under, h])
  have hsph := GlobalTheory.SphLoc.isSpherical_of_sphAt π s' σ hσ (hv ▸ hs)
  have hu := (GlobalTheory.CuspRep.ParLaws.unr_iff (GlobalTheory.CuspRep.ParLaws.isRec_locRec hL (D.nd.plOm.2 s'.w)) σ).2 hsph
  have key : ∀ (u u' : HeightOneSpectrum (𝓞 D.host.E)) (_ : u = u') (a : GlobalTheory.LocGL.IrrGL (u.adicCompletion D.host.E))
      (b : GlobalTheory.LocGL.IrrGL (u'.adicCompletion D.host.E)), HEq a b →
      (GlobalTheory.CuspRep.ParLaws.locRec hL (D.nd.plOm.2 u) a).unr → (GlobalTheory.CuspRep.ParLaws.locRec hL (D.nd.plOm.2 u') b).unr := by
    intro u u' hu a b hab
    subst hu
    cases eq_of_heq hab
    exact id
  exact key _ _ h _ _ e hu

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfInducedOfInduced
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.HermIsom Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.NefFibUniq

theorem nefFib_shift {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (L : HermLB p) (t : (k →+* ℂ) → ℝ)
    (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) : ArInt.NefFib (L.shift t ht) ↔ ArInt.NefFib L := Iff.rfl

theorem nefFib_iff_of_isometric {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {L L' : HermLB p}
    (h : L.Isometric L') : ArInt.NefFib L ↔ ArInt.NefFib L' := by
  obtain ⟨w, hw, -⟩ := h
  have e : cls L.B L.isLB = cls L'.B L'.isLB := (cls_eq_iff _ _).2 ⟨w, hw⟩
  have key : ∀ (Z : Scheme.{0}) (i : Z ⟶ X) (κ : Type) [Field κ] [Algebra κ Γ(Z, ⊤)],
      topSelfIntersection κ (L.B.pull i) 1 = topSelfIntersection κ (L'.B.pull i) 1 := fun Z i κ _ _ =>
    interNum_congr_cls κ _ (fun _ => LB.isLB_pull L.isLB i) (fun _ => LB.isLB_pull L'.isLB i) fun _ => by
      rw [cls_pull L.isLB, cls_pull L'.isLB, e]
  constructor <;> intro H Z i _ _ κ _ _ _ hd
  · rw [← key]; exact H Z i κ hd
  · rw [key]; exact H Z i κ hd

variable {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F} {A : Adl C Y}

theorem surjective_of_models (M N : TrueGeo.Model Y) (π : N.X ⟶ M.X) (hπ : π ≫ M.p = N.p)
    (hU : ∃ U : M.X.Opens, (U : Set M.X).Nonempty ∧ IsIso (π ∣_ U)) : Function.Surjective π := by
  obtain ⟨U, hne, hi⟩ := hU
  have := M.ar.isIntegral
  have := N.ar.isIntegral
  have : IsProper M.p := CommonModel.isProper_of_isProjOver M.ar.isProjOver
  have : IsProper N.p := CommonModel.isProper_of_isProjOver N.ar.isProjOver
  have : IsProper (π ≫ M.p) := by rw [hπ]; infer_instance
  have : IsProper π := IsProper.of_comp π M.p
  obtain ⟨_, _⟩ := birational_of_isIso_morphismRestrict π U hne.to_subtype
  exact (surjective_of_isDominant_of_isClosed_range π π.isClosedMap.isClosed_range).surj

theorem nefFib_of_induced_of_induced (N : TrueGeo.Model Y) (hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme N.X)
    {L L' : HermLB N.p} {k : ℕ+} {cf cf' : HeightOneSpectrum (𝓞 F) → ℝ}
    (h : A.Induced N L k cf) (h' : A.Induced N L' k cf') (hL' : ArInt.NefFib L') : ArInt.NefFib L := by
  have hint := N.ar.isIntegral
  have hproj := N.ar.isProjOver
  obtain ⟨m, b, b', hb, hb', e⟩ := GlobalTheory.exists_mul_eq_log_adicAbv_sub F (fun v => ((k : ℕ) : ℝ) * (A.n : ℕ) * (cf' v - cf v))
    ((h.1.union h'.1).subset fun v hv => by
      by_contra h0
      simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h0
      simp [h0.1, h0.2] at hv) fun v => by
    obtain ⟨e, α, hα, h₁⟩ := GlobalTheory.TrueGeo.ValGroup.main F C Y A N L L' k cf cf' h h' v
    rw [h₁]
    exact GlobalTheory.ExtValueGroup.log_w_rat F v e α hα
  have hc : ∀ σ : 𝓞 F →+* ℂ, Real.log ‖((starRingEnd ℂ).comp σ) b‖ = Real.log ‖σ b‖ := fun σ => by simp
  have hc' : ∀ σ : 𝓞 F →+* ℂ, Real.log ‖((starRingEnd ℂ).comp σ) b'‖ = Real.log ‖σ b'‖ := fun σ => by simp
  have h₁ := GlobalTheory.TrueGeo.IndScale.induced_shift F C Y A N (L.pow m) (k * m) cf b hb hc (GlobalTheory.TrueGeo.InducedPow.induced_pow F C Y A N L k m cf h)
  have h₂ := GlobalTheory.TrueGeo.IndScale.induced_shift F C Y A N (L'.pow m) (k * m) cf' b' hb' hc' (GlobalTheory.TrueGeo.InducedPow.induced_pow F C Y A N L' k m cf' h')
  have hm : ((m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast m.ne_zero
  have hk : ((k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast k.ne_zero
  have hn : ((A.n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast A.n.ne_zero
  have h₂' : A.Induced N ((L'.pow m).shift (fun σ => Real.log ‖σ b'‖) hc') (k * m) fun v => cf v +
      Real.log (NumberField.HeightOneSpectrum.adicAbv F v (algebraMap (𝓞 F) F b)) / ((((k * m : ℕ+) : ℕ) : ℝ) * (A.n : ℕ)) := by
    convert h₂ using 2 with v
    rw [sub_eq_iff_eq_add.1 (e v).symm, PNat.mul_coe, Nat.cast_mul]
    field_simp
    ring
  have hR := GlobalTheory.TrueGeo.InducedIsom.ratIsom_of_induced F C Y A N hN _ _ (k * m) _ h₁ h₂'
  have hIso := GlobalTheory.HermIsom.isometric_of_ratIsom _ N.X N.p _ _ hR
  have hL'm : ArInt.NefFib ((L'.pow m).shift (fun σ => Real.log ‖σ b'‖) hc') :=
    (nefFib_shift _ _ _).2 ((GlobalTheory.T.nefFib_pow_iff' _ N.X N.p hproj L' m m.pos).2 hL')
  exact (GlobalTheory.T.nefFib_pow_iff' _ N.X N.p hproj L m m.pos).1 ((nefFib_shift _ _ _).1 ((nefFib_iff_of_isometric hIso).2 hL'm))

theorem nefFib_of_induced : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y)
    (M : TrueGeo.Model Y) (L : HermLB M.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ),
    A.Induced M L k cf → A.NefFib → ArInt.NefFib L := by
  rintro F _ _ C Y A M L k cf hI ⟨M', L', k', cf', hI', hN'⟩
  obtain ⟨N, π, π', hN, hπ, hπ', hj, hj', hU, hU'⟩ := GlobalTheory.ModelDom.exists_normal_dominating F Y M M'
  have := M.ar.isIntegral
  have := M'.ar.isIntegral
  have := N.ar.isIntegral
  have h₁ := GlobalTheory.TrueGeo.InducedPow.induced_pow F C Y A N _ k k' cf (GlobalTheory.TrueGeo.InducedPull.induced_pull F C Y A M N π hπ hj L k cf hI)
  have h₂ := GlobalTheory.TrueGeo.InducedPow.induced_pow F C Y A N _ k' k cf' (GlobalTheory.TrueGeo.InducedPull.induced_pull F C Y A M' N π' hπ' hj' L' k' cf' hI')
  rw [mul_comm k' k] at h₂
  have hN₂ : ArInt.NefFib ((L'.pull π' hπ').pow k) :=
    (GlobalTheory.T.nefFib_pow_iff' _ N.X N.p N.ar.isProjOver _ k k.pos).2 (GlobalTheory.T.nefFib_pullback _ M'.X N.X M'.p N.p M'.ar.isProjOver N.ar.isProjOver π' hπ' L' hN')
  have hN₁ := nefFib_of_induced_of_induced N hN h₁ h₂ hN₂
  exact GlobalTheory.T.nefFib_of_surjective_pullback _ M.X N.X M.p N.p M.ar.isProjOver N.ar.isProjOver π hπ (surjective_of_models M N π hπ hU) L
    ((GlobalTheory.T.nefFib_pow_iff' _ N.X N.p N.ar.isProjOver _ k' k'.pos).1 hN₁)

end GlobalTheory.TrueGeo.NefFibUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ParahoricCharacterMulOfTame
section
noncomputable section

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory.Mem.LamMul

section Blocks

variable {S : Type*} [CommRing S] {r c : ℕ}

theorem det_eq_of_lower_zero (M : Matrix (Fin (r + c)) (Fin (r + c)) S)
    (h : M.submatrix (Fin.natAdd r) (Fin.castAdd c) = 0) :
    M.det = (M.submatrix (Fin.castAdd c) (Fin.castAdd c)).det * (M.submatrix (Fin.natAdd r) (Fin.natAdd r)).det := by
  have e : M.submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks (M.submatrix (Fin.castAdd c) (Fin.castAdd c)) (M.submatrix (Fin.castAdd c) (Fin.natAdd r)) 0
        (M.submatrix (Fin.natAdd r) (Fin.natAdd r)) := by
    rw [← h]
    ext (i | i) (j | j) <;> simp
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv M, e, Matrix.det_fromBlocks_zero₂₁]

theorem mul_dd_of_lower_zero (M N : Matrix (Fin (r + c)) (Fin (r + c)) S)
    (h : M.submatrix (Fin.natAdd r) (Fin.castAdd c) = 0) :
    (M * N).submatrix (Fin.natAdd r) (Fin.natAdd r) =
      M.submatrix (Fin.natAdd r) (Fin.natAdd r) * N.submatrix (Fin.natAdd r) (Fin.natAdd r) := by
  ext i j
  have h0 : ∀ a, M (Fin.natAdd r i) (Fin.castAdd c a) = 0 := fun a => congrFun (congrFun h i) a
  simp [Matrix.mul_apply, Fin.sum_univ_add, h0]

theorem dd_mod (I : Ideal S) (K K' : Matrix (Fin (r + c)) (Fin (r + c)) S)
    (hK : ∀ i j, K (Fin.natAdd r i) (Fin.castAdd c j) ∈ I) (hK' : ∀ i j, K' (Fin.natAdd r i) (Fin.castAdd c j) ∈ I)
    (hu : IsUnit K.det) (hu' : IsUnit K'.det) :
    IsUnit (Ideal.Quotient.mk I (K.submatrix (Fin.natAdd r) (Fin.natAdd r)).det) ∧
    IsUnit (Ideal.Quotient.mk I (K'.submatrix (Fin.natAdd r) (Fin.natAdd r)).det) ∧
    ((K * K').submatrix (Fin.natAdd r) (Fin.natAdd r)).det -
      (K.submatrix (Fin.natAdd r) (Fin.natAdd r)).det * (K'.submatrix (Fin.natAdd r) (Fin.natAdd r)).det ∈ I := by
  have key : ∀ X : Matrix (Fin (r + c)) (Fin (r + c)) S, (∀ i j, X (Fin.natAdd r i) (Fin.castAdd c j) ∈ I) →
      ((Ideal.Quotient.mk I).mapMatrix X).submatrix (Fin.natAdd r) (Fin.castAdd c) = 0 := by
    intro X hX
    ext i j
    simpa [Ideal.Quotient.eq_zero_iff_mem] using hX i j
  have sub : ∀ X : Matrix (Fin (r + c)) (Fin (r + c)) S, Ideal.Quotient.mk I (X.submatrix (Fin.natAdd r) (Fin.natAdd r)).det =
      (((Ideal.Quotient.mk I).mapMatrix X).submatrix (Fin.natAdd r) (Fin.natAdd r)).det := by
    intro X
    rw [RingHom.map_det]
    rfl
  have unit : ∀ X : Matrix (Fin (r + c)) (Fin (r + c)) S, (∀ i j, X (Fin.natAdd r i) (Fin.castAdd c j) ∈ I) →
      IsUnit X.det → IsUnit (Ideal.Quotient.mk I (X.submatrix (Fin.natAdd r) (Fin.natAdd r)).det) := by
    intro X hX hu
    have h1 : IsUnit ((Ideal.Quotient.mk I).mapMatrix X).det := by
      rw [← RingHom.map_det]
      exact hu.map _
    rw [det_eq_of_lower_zero _ (key X hX)] at h1
    rw [sub]
    exact isUnit_of_mul_isUnit_right h1
  refine ⟨unit K hK hu, unit K' hK' hu', ?_⟩
  rw [← Ideal.Quotient.eq, map_mul, sub, sub, sub, map_mul,
    mul_dd_of_lower_zero _ _ (key K hK), Matrix.det_mul]

end Blocks

section Val

variable {F Γ : Type} [Field F] [LinearOrderedCommGroupWithZero Γ] (v : Valuation F Γ) (O : Subring F) (ε : Γ)

def redI (hO : ∀ x ∈ O, v x ≤ 1) : Ideal O where
  carrier := {a | v (a : F) ≤ ε}
  add_mem' {a b} ha hb := by
    show v ((a : F) + b) ≤ ε
    exact (v.map_add _ _).trans (max_le ha hb)
  zero_mem' := by
    show v ((0 : O) : F) ≤ ε
    simp
  smul_mem' a b hb := by
    show v ((a : F) * b) ≤ ε
    rw [map_mul]
    exact (mul_le_of_le_one_left' (hO _ a.2)).trans hb

variable {v O ε}

theorem val_eq_one_of_isUnit (hO : ∀ x ∈ O, v x ≤ 1) (hε : ε < 1) (a : O)
    (h : IsUnit (Ideal.Quotient.mk (redI v O ε hO) a)) : v (a : F) = 1 := by
  obtain ⟨b, hb⟩ := h.exists_right_inv
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  have h1 : a * b - 1 ∈ redI v O ε hO := by
    apply Ideal.Quotient.eq.1
    simpa using hb
  have h2 : v ((a : F) * b - 1) ≤ ε := by
    have h1' : v (((a * b - 1 : O)) : F) ≤ ε := h1
    simpa using h1'
  have h3 : v ((a : F) * b) = 1 := by
    have e : (a : F) * b = ((a : F) * b - 1) + 1 := by ring
    rw [e, Valuation.map_add_eq_of_lt_right]
    · simp
    · simpa using h2.trans_lt hε
  rw [map_mul] at h3
  refine le_antisymm (hO _ a.2) ?_
  rw [← h3]
  exact mul_le_of_le_one_right' (hO _ b.2)

omit [LinearOrderedCommGroupWithZero Γ] in

theorem exists_lift {n : ℕ} {k : GL (Fin n) F} (hk : k ∈ GLint O n) :
    ∃ K : Matrix (Fin n) (Fin n) O, (k : Matrix (Fin n) (Fin n) F) = K.map O.subtype ∧ IsUnit K.det := by
  let K : Matrix (Fin n) (Fin n) O := fun i j => ⟨(k : Matrix (Fin n) (Fin n) F) i j, hk.1 i j⟩
  let K' : Matrix (Fin n) (Fin n) O := fun i j => ⟨((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j, hk.2 i j⟩
  have e : (k : Matrix (Fin n) (Fin n) F) = K.map O.subtype := by ext i j; rfl
  have e' : ((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = K'.map O.subtype := by ext i j; rfl
  refine ⟨K, e, Matrix.isUnit_det_of_right_inverse (B := K') ?_⟩
  apply Matrix.map_injective (f := O.subtype) Subtype.val_injective
  show (K * K').map O.subtype = (1 : Matrix (Fin n) (Fin n) O).map O.subtype
  rw [Matrix.map_mul, ← e, ← e', ← Units.val_mul, mul_inv_cancel, Matrix.map_one _ (map_zero _) (map_one _)]
  rfl

omit [LinearOrderedCommGroupWithZero Γ] in
theorem det_dd_map {r c : ℕ} (K : Matrix (Fin (r + c)) (Fin (r + c)) O) :
    (bDD (K.map O.subtype)).det = (((K.submatrix (Fin.natAdd r) (Fin.natAdd r)).det : O) : F) := by
  show _ = O.subtype _
  rw [RingHom.map_det]
  rfl

theorem dd_val (hO : ∀ x ∈ O, v x ≤ 1) (hε : ε < 1) {r c : ℕ} {k k' : GL (Fin (r + c)) F}
    (hk : k ∈ GLint O (r + c)) (hk' : k' ∈ GLint O (r + c))
    (hd : ∀ i j, v ((k : Matrix (Fin (r + c)) (Fin (r + c)) F) (Fin.natAdd r i) (Fin.castAdd c j)) ≤ ε)
    (hd' : ∀ i j, v ((k' : Matrix (Fin (r + c)) (Fin (r + c)) F) (Fin.natAdd r i) (Fin.castAdd c j)) ≤ ε) :
    v (bDD (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det = 1 ∧
    v (bDD (k' : Matrix (Fin (r + c)) (Fin (r + c)) F)).det = 1 ∧
    v ((bDD ((k * k' : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F)).det -
      (bDD (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det * (bDD (k' : Matrix (Fin (r + c)) (Fin (r + c)) F)).det) ≤ ε := by
  obtain ⟨K, e, hu⟩ := exists_lift hk
  obtain ⟨K', e', hu'⟩ := exists_lift hk'
  have hK : ∀ i j, K (Fin.natAdd r i) (Fin.castAdd c j) ∈ redI v O ε hO := fun i j => by
    have := hd i j
    rw [e] at this
    exact this
  have hK' : ∀ i j, K' (Fin.natAdd r i) (Fin.castAdd c j) ∈ redI v O ε hO := fun i j => by
    have := hd' i j
    rw [e'] at this
    exact this
  obtain ⟨h1, h2, h3⟩ := dd_mod (redI v O ε hO) K K' hK hK' hu hu'
  have em : ((k * k' : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = (K * K').map O.subtype := by
    rw [Units.val_mul, e, e', Matrix.map_mul]
  rw [em, e, e', det_dd_map, det_dd_map, det_dd_map]
  refine ⟨val_eq_one_of_isUnit hO hε _ h1, val_eq_one_of_isUnit hO hε _ h2, ?_⟩
  have h3' : v (((((K * K').submatrix (Fin.natAdd r) (Fin.natAdd r)).det -
      (K.submatrix (Fin.natAdd r) (Fin.natAdd r)).det * (K'.submatrix (Fin.natAdd r) (Fin.natAdd r)).det : O)) : F) ≤ ε := h3
  simpa using h3'

end Val

section Main

theorem lamJ_mul : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (δ : (P.adicCompletion L)ˣ →* ℂˣ), IsDel P δ → ∀ (r c : ℕ) (k k' : GL (Fin (r + c)) (P.adicCompletion L)), k ∈ parJ (OP P) (piP P : P.adicCompletion L) r c → k' ∈ parJ (OP P) (piP P : P.adicCompletion L) r c → lamJ δ (k * k') = lamJ δ k * lamJ δ k' := by
  intro L _ _ P δ hδ r c k k' hk hk'
  have hO : ∀ x ∈ OP P, Valued.v x ≤ 1 := fun x hx => hx
  have hε : (WithZero.exp (-1 : ℤ)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have hπ : Valued.v (piP P : P.adicCompletion L) = WithZero.exp (-1 : ℤ) := unif_spec P
  have small : ∀ {g : GL (Fin (r + c)) (P.adicCompletion L)}, g ∈ parJ (OP P) (piP P : P.adicCompletion L) r c →
      ∀ i j, Valued.v ((g : Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L)) (Fin.natAdd r i) (Fin.castAdd c j)) ≤
        WithZero.exp (-1 : ℤ) := by
    intro g hg i j
    obtain ⟨o, ho, e⟩ := hg.2 i j
    have e' : (g : Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L)) (Fin.natAdd r i) (Fin.castAdd c j) =
        (piP P : P.adicCompletion L) * o := e
    rw [e', map_mul, hπ]
    exact mul_le_of_le_one_right' (hO _ ho)
  obtain ⟨ha, hb, hxy⟩ := dd_val hO hε hk.1 hk'.1 (small hk) (small hk')
  unfold lamJ
  set a := (bDD (k : Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L))).det with hadef
  set b := (bDD (k' : Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L))).det with hbdef
  set x := (bDD ((k * k' : GL (Fin (r + c)) (P.adicCompletion L)) : Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L))).det with hxdef
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hb0 : b ≠ 0 := fun h => by simp [h] at hb
  have hab : Valued.v (a * b) = 1 := by rw [map_mul, ha, hb, one_mul]
  have hx : Valued.v x = 1 := by
    have e : x = (x - a * b) + a * b := by ring
    rw [e, Valuation.map_add_eq_of_lt_right, hab]
    rw [hab]
    exact hxy.trans_lt hε
  have hx0 : x ≠ 0 := fun h => by simp [h] at hx
  have tame := hδ.tame (Units.mk0 x hx0 * (Units.mk0 a ha0 * Units.mk0 b hb0)⁻¹) (by
    show Valued.v _ = 1
    simp [hx, ha, hb]) (by
    have e : x * (a * b)⁻¹ - 1 = (x - a * b) * (a * b)⁻¹ := by field_simp
    simp only [Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val]
    rw [e, map_mul, map_inv₀, hab, inv_one, mul_one]
    exact hxy)
  rw [map_mul, map_inv, mul_inv_eq_one, map_mul] at tame
  simp only [chi0, dif_neg hx0, dif_neg ha0, dif_neg hb0, tame, Units.val_mul]

end Main

end GlobalTheory.Mem.LamMul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelIndexLevelUnipotentCoprimePrimeStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.L2
open Formalism.AUTREP (GAf)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_levelUnipotent_coprime_prime : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (r p : ℕ) (H : Subgroup (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)))), p.Prime → s.Above p → r ≤ n → (∀ g, g ∈ H ↔ NG.UniRT s r g) → Nat.Coprime (H.relIndex (Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring)) p := by
  first | exact @GlobalTheory.UniLevelIndex.relIndex_coprime | exact GlobalTheory.UniLevelIndex.relIndex_coprime | (intros; apply GlobalTheory.UniLevelIndex.relIndex_coprime <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelIndexStabilizerEqLocalRelIndexStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.L2
open Formalism.AUTREP (GAf)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_stabilizer_eq_local_relIndex : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (J : Subgroup (GAf L n)) (H : Subgroup (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)))), (∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ s.loc n κ ∈ H)) → J.relIndex (GlobalTheory.HeckeScalarSph.locK n s.v) = H.relIndex (Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring) := by
  first | exact @GlobalTheory.LocRelIndex.main | exact GlobalTheory.LocRelIndex.main | (intros; apply GlobalTheory.LocRelIndex.main <;> assumption)
end

