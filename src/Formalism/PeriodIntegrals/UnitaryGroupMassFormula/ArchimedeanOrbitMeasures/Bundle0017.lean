import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0016
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.Bundle0004
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.Bundle0003
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PushInv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0010
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0011
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0012
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.T2SpaceTensorProductFiniteExtension

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.EqOneOfToHAFin
section
noncomputable section

open MeasureTheory NumberField Set
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets
open scoped TensorProduct

namespace PI.AprimeInfU

theorem tauF_eq_comm {D : D7} (X : HidaSetting D) (y : AF X.B.I.F ⊗[X.B.I.F] X.B.I.E) :
    tauF X.B.I y = Algebra.TensorProduct.comm X.B.I.F (Af X.B.I.F) X.B.I.E
      (tensMap (E := X.B.I.E) (sndA X.B.I.F) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [tauF_tmul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem toHA_fin_one {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (s : X.B.I.Ginf) :
    (splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb (s, 1))).2 = 1 := by
  have hbr := ((toHA_isBridge X.B.I hb) (s, 1)).2
  apply Subtype.ext
  apply Units.ext
  ext i j
  have e := congrFun (congrFun hbr i) j
  simp only [ofHAFin, Matrix.map_apply] at e
  rw [tauF_eq_comm] at e
  have e2 := congrArg (Algebra.TensorProduct.comm X.B.I.F (Af X.B.I.F) X.B.I.E).symm e
  rw [AlgEquiv.symm_apply_apply] at e2
  show tensMap (E := X.B.I.E) (sndA X.B.I.F) _ = _
  rw [← e2]
  show _ = (1 : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E)) i j
  simp only [Formalism.MainNotions.S.AutInst.fmat, OneMemClass.coe_one, Units.val_one, Matrix.one_apply]
  split_ifs <;> simp

theorem eq_one_of_toHA_fin {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (p : X.B.I.GA)
    (h : (splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb p)).2 = 1) : p.2 = 1 := by
  have hbr := ((toHA_isBridge X.B.I hb) p).2
  apply Subtype.ext
  apply Units.ext
  ext i j
  have e := congrFun (congrFun hbr i) j
  simp only [ofHAFin, Matrix.map_apply] at e
  rw [tauF_eq_comm] at e
  have h2 : tensMap (E := X.B.I.E) (sndA X.B.I.F) (hmat X.B.I (toHA X.B.I hb p) i j) =
      (1 : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E)) i j := by
    have := congrArg (fun g : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J =>
      (HA.mat (Af X.B.I.F) X.B.I.cm.sig X.B.I.J g).val i j) h
    exact this
  rw [h2] at e
  rw [Formalism.MainNotions.S.AutInst.fmat] at e
  show _ = (1 : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) i j
  rw [e, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

section Bridge

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

def evInf (v : InfinitePlace X.B.I.F) : Ainf X.B.I.F →+* ℂ :=
  (InfinitePlace.Completion.extensionEmbedding v).comp
    (Pi.evalRingHom (fun w : InfinitePlace X.B.I.F => w.Completion) v)

def thetaInf (v : InfinitePlace X.B.I.F) : Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E →+* ℂ :=
  letI : Algebra X.B.I.F ℂ := v.embedding.toAlgebra
  (Algebra.TensorProduct.lift
    ({ evInf X v with commutes' := fun a => evV_algebraMap X.B.I v a } : Ainf X.B.I.F →ₐ[X.B.I.F] ℂ)
    ({ X.B.I.φ v with commutes' := X.B.I.φ_over v } : X.B.I.E →ₐ[X.B.I.F] ℂ)
    (fun _ _ => Commute.all _ _)).toRingHom

theorem thetaV_eq (v : InfinitePlace X.B.I.F) (y : AF X.B.I.F ⊗[X.B.I.F] X.B.I.E) :
    thetaV X.B.I v y = thetaInf X v (tensMap (E := X.B.I.E) (fstA X.B.I.F) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [thetaV_tmul]
    simp only [thetaInf, tensMap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      Algebra.TensorProduct.lift_tmul, AlgHom.id_apply]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem ofHAInf_congr (a b : HAd X.B.I)
    (h : (splitA X.B.I.cm.sig X.B.I.J a).1 = (splitA X.B.I.cm.sig X.B.I.J b).1) :
    ofHAInf X.B.I a = ofHAInf X.B.I b := by
  funext v
  unfold ofHAInf
  congr 2
  ext i j
  simp only [Matrix.map_apply, thetaV_eq]
  have := congrArg (fun g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J =>
    (HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g).val i j) h
  exact congrArg (thetaInf X v) this

theorem ofHAFin_congr (a b : HAd X.B.I)
    (h : (splitA X.B.I.cm.sig X.B.I.J a).2 = (splitA X.B.I.cm.sig X.B.I.J b).2) :
    ofHAFin X.B.I a = ofHAFin X.B.I b := by
  unfold ofHAFin
  ext i j
  simp only [Matrix.map_apply, tauF_eq_comm]
  have := congrArg (fun g : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J =>
    (HA.mat (Af X.B.I.F) X.B.I.cm.sig X.B.I.J g).val i j) h
  exact congrArg (Algebra.TensorProduct.comm X.B.I.F (Af X.B.I.F) X.B.I.E) this

theorem eq_of_ofHA (p q : X.B.I.GA) (h1 : ofHAInf X.B.I (toHA X.B.I hb p) = ofHAInf X.B.I (toHA X.B.I hb q))
    (h2 : ofHAFin X.B.I (toHA X.B.I hb p) = ofHAFin X.B.I (toHA X.B.I hb q)) : p = q := by
  obtain ⟨a₁, b₁⟩ := (toHA_isBridge X.B.I hb) p
  obtain ⟨a₂, b₂⟩ := (toHA_isBridge X.B.I hb) q
  refine Prod.ext (funext fun v => ?_) ?_
  · exact Subtype.ext (Units.ext ((a₁ v).trans ((congrFun h1 v).trans (a₂ v).symm)))
  · exact Subtype.ext (Units.ext (b₁.trans (h2.trans b₂.symm)))

theorem toInf_mul (s t : X.B.I.Ginf) : X.toInf hb (s * t) = X.toInf hb s * X.toInf hb t := by
  have e : ((s * t, 1) : X.B.I.GA) = (s, 1) * (t, 1) := by simp
  show (splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb (s * t, 1))).1 = _
  rw [e, map_mul, map_mul]
  rfl

theorem toHA_inf_one (hS : MassDataMassesW.SplitIso) (x : X.B.I.Gf) :
    (splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb (1, x))).1 = 1 := by
  obtain ⟨e, he⟩ := hS X.B.I.cm.sig X.B.I.J
  set h := toHA X.B.I hb (1, x) with hh
  set h' := e.symm (1, (splitA X.B.I.cm.sig X.B.I.J h).2) with hh'
  have hs' : splitA X.B.I.cm.sig X.B.I.J h' = (1, (splitA X.B.I.cm.sig X.B.I.J h).2) := by
    have h0 := e.apply_symm_apply (1, (splitA X.B.I.cm.sig X.B.I.J h).2)
    rw [he] at h0
    exact h0
  set q := (toHA X.B.I hb).symm h' with hq
  have hqh : toHA X.B.I hb q = h' := (toHA X.B.I hb).apply_symm_apply h'
  have h1 : ofHAInf X.B.I (toHA X.B.I hb q) = ofHAInf X.B.I (toHA X.B.I hb (1, 1)) := by
    rw [hqh]
    apply ofHAInf_congr
    rw [hs', show ((1, 1) : X.B.I.GA) = 1 from rfl, map_one, map_one]
    rfl
  have h1' : ofHAInf X.B.I (toHA X.B.I hb (1, 1)) = ofHAInf X.B.I (toHA X.B.I hb (1, x)) := by
    obtain ⟨a₁, -⟩ := (toHA_isBridge X.B.I hb) (1, 1)
    obtain ⟨a₂, -⟩ := (toHA_isBridge X.B.I hb) (1, x)
    funext v
    exact (a₁ v).symm.trans (a₂ v)
  have h2 : ofHAFin X.B.I (toHA X.B.I hb q) = ofHAFin X.B.I (toHA X.B.I hb (1, x)) := by
    rw [hqh]
    apply ofHAFin_congr
    rw [hs']
  have hq1 : q = (1, x) := eq_of_ofHA X hb q (1, x) (h1.trans h1') h2
  have : h' = h := by rw [← hqh, hq1]
  rw [← this, hs']

theorem split_toHA (hS : MassDataMassesW.SplitIso) (p : X.B.I.GA) :
    splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb p) = (X.toInf hb p.1, finHA X hb p.2) := by
  have e : p = (p.1, 1) * (1, p.2) := by simp
  conv_lhs => rw [e, map_mul, map_mul]
  refine Prod.ext ?_ ?_
  · show X.toInf hb p.1 * (splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb (1, p.2))).1 = _
    rw [toHA_inf_one X hb hS, mul_one]
  · show (splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb (p.1, 1))).2 * finHA X hb p.2 = _
    rw [toHA_fin_one X hb, one_mul]

theorem toInf_surjective (hS : MassDataMassesW.SplitIso) : Function.Surjective (X.toInf hb) := by
  intro y
  obtain ⟨e, he⟩ := hS X.B.I.cm.sig X.B.I.J
  set p := (toHA X.B.I hb).symm (e.symm (y, 1))
  have hp : splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb p) = (y, 1) := by
    rw [← he]
    simp [p]
  have h2 : p.2 = 1 := eq_one_of_toHA_fin X hb p (by rw [hp])
  refine ⟨p.1, ?_⟩
  have := congrArg Prod.fst hp
  rw [split_toHA X hb hS] at this
  exact this

end Bridge

end PI.AprimeInfU
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.OrbPolD
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem gramR_Y0_eq_TI {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)
    (hT : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
      gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j) :
    gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (Y0 X u') = ((TI X u' hT : HermR _ _ _) : Matrix _ _ _) := by
  rw [show Y0 X u' = orbM X u' 1 from (one_smul _ _).symm, orbM, gramR_smul, gramR_ratTup]
  rfl

theorem indI_of_gram {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)
    (hT : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
      gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j)
    (hd : (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det ≠ 0) (Y : TupI X)
    (hY : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J Y = ((TI X u' hT : HermR _ _ _) : Matrix _ _ _)) :
    Y ∈ IndI X := by
  have e1 := orbM_mem X u' hT hd 1
  have e0 : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J Y =
      gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (orbM X u' 1) := by rw [hY, e1.1]
  apply linIndep_of_isUnit_det (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J
  rw [e0, e1.1]
  have e2 := RingHom.map_det (inclR (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F))
    (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')))
  rw [RingHom.mapMatrix_apply] at e2
  show IsUnit ((gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Ainf X.B.I.F))).det
  rw [← e2]
  exact (isUnit_iff_ne_zero.2 hd).map _

theorem fib_near (hR : RmulFacts) (hF : FibAllT) (hC : MassDataMassesW.HinfCompact) {D : D7} (X : HidaSetting D)
    (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf
    (hP : PushHyp X u' ψ hT μinf νinf fibInf) (T : HmI X) (a : MfI X) (hunit : IsUnit a)
    (hgT : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (rmulT X a (Y0 X u')) = (T : Matrix _ _ _))
    (hind : ∀ Y : TupI X, gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J Y = (T : Matrix _ _ _) → Y ∈ IndI X) :
    ∃ c : ENNReal, fibInf T = c • X.measG.μGinf.map (fun g => g • rmulT X a (Y0 X u')) := by
  obtain ⟨hmr, hcomp, hsmul, hgram, hcTmul, hcT1, hKm, hrc⟩ := hR X
  have hd := detNZ_holds X u' ψ hT μinf νinf fibInf hP
  have hfib := hP.2.2.2.2.2.2
  obtain ⟨hinvT, hlfT⟩ := hF X u' ψ hT μinf νinf fibInf hP T
  set b : MfI X := ↑hunit.unit⁻¹ with hb
  have hab : a * b = 1 := hunit.mul_val_inv
  have hba : b * a = 1 := hunit.val_inv_mul
  have hab' : ∀ Y, rmulT X a (rmulT X b Y) = Y := fun Y => by rw [hcomp, hba, rmulT_one]
  have hba' : ∀ Y, rmulT X b (rmulT X a Y) = Y := fun Y => by rw [hcomp, hab, rmulT_one]
  set ν := (fibInf T).map (rmulT X b) with hν
  have i1 : InvI X ν := by
    intro g
    rw [hν, Measure.map_map (measurable_smul_tupI X g) (hmr b)]
    have : ((fun y => g • y) ∘ rmulT X b) = rmulT X b ∘ (fun y => g • y) := funext fun y => hsmul g b y
    rw [this, ← Measure.map_map (hmr b) (measurable_smul_tupI X g), hinvT g]
  have hS : fibInf T (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {T.1} ∩ IndI X)ᶜ = 0 :=
    hfib.1 T
  have s1 : ν (FbI X u' hT)ᶜ = 0 := by
    rw [hν, Measure.map_apply (hmr b) (measurableSet_FbI X u' hT).compl]
    refine measure_mono_null ?_ hS
    intro y hy hy2
    apply hy
    have hg : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (rmulT X b y) = ((TI X u' hT : HermR _ _ _) : Matrix _ _ _) := by
      rw [hgram, hy2.1, ← hgT, hgram, gramR_Y0_eq_TI X u' hT, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hcTmul,
        Matrix.mul_assoc, hab, hcT1, Matrix.one_mul, Matrix.mul_one]
    exact ⟨hg, indI_of_gram X u' hT hd _ hg⟩
  have l1 : LFI X ν := by
    intro K hK hKI
    rw [hν, Measure.map_apply (hmr b) (hKm K hK)]
    have hpre : rmulT X b ⁻¹' K = rmulT X a '' K := by
      ext y
      constructor
      · intro hy; exact ⟨rmulT X b y, hy, hab' y⟩
      · rintro ⟨k, hk, rfl⟩; show rmulT X b (rmulT X a k) ∈ K; rw [hba']; exact hk
    rw [hpre]
    have hcl : IsClosed (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {T.1}) := by
      haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
      exact isClosed_singleton.preimage (continuous_gramRP (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)
    have hK2 : IsCompact (rmulT X a '' K ∩ gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {T.1}) :=
      (hK.image (hrc a)).inter_right hcl
    calc fibInf T (rmulT X a '' K)
        ≤ fibInf T (rmulT X a '' K ∩ gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {T.1}) +
          fibInf T (rmulT X a '' K \ gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {T.1}) :=
          measure_le_inter_add_sdiff _ _ _
      _ = fibInf T (rmulT X a '' K ∩ gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {T.1}) := by
          have h0 : fibInf T (rmulT X a '' K \ gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {T.1}) = 0 := by
            refine measure_mono_null ?_ hS
            intro y hy hy2
            exact hy.2 hy2.1
          rw [h0, add_zero]
      _ < ⊤ := hlfT _ hK2 (fun y hy => hind y hy.2)
  obtain ⟨c, -, hc⟩ := orbRep_of_witt wittInf_holds hC X u' ψ hT μinf νinf fibInf hP ν i1 s1 l1
  refine ⟨c, ?_⟩
  have e1 : fibInf T = ν.map (rmulT X a) := by
    rw [hν, Measure.map_map (hmr a) (hmr b)]
    have : rmulT X a ∘ rmulT X b = id := funext hab'
    rw [this, Measure.map_id]
  have e2 : (fun g => g • rmulT X a (Y0 X u')) = rmulT X a ∘ orbM X u' :=
    funext fun g => hsmul g a (Y0 X u')
  rw [e1, hc, Measure.map_smul, e2, Measure.map_map (hmr a) (measurable_orbM X u')]

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ProperW
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem fbI_closed {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)
    (hT : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
      gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j)
    (hd : (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det ≠ 0) : IsClosed (FbI X u' hT) := by
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have hdet : ((gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (F := X.B.I.F) (Ainf X.B.I.F))).det =
      inclR (F := X.B.I.F) (Ainf X.B.I.F) (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det := by
    rw [RingHom.map_det]; rfl
  have hsub : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {((TI X u' hT : HmI X) : Matrix _ _ _)} ⊆ IndI X := by
    intro y hy
    have hy' : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J y = ((TI X u' hT : HmI X) : Matrix _ _ _) := hy
    apply linIndep_of_isUnit_det (R := Ainf X.B.I.F) (σ := X.B.I.cm.sig) (J := X.B.I.J) y
    rw [hy']
    show IsUnit ((gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (F := X.B.I.F) (Ainf X.B.I.F))).det
    rw [hdet]
    exact (isUnit_iff_ne_zero.2 hd).map _
  have he : FbI X u' hT = gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {((TI X u' hT : HmI X) : Matrix _ _ _)} :=
    Set.inter_eq_left.2 hsub
  rw [he]
  exact isClosed_singleton.preimage (continuous_gramI X)

theorem properOne_of (hW : WittInf) (hH : MassDataMassesW.HinfCompact) : ProperOne := by
  intro D X u' ψ hT μinf νinf fibInf hP K hK
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have : SecondCountableTopology (GI X) :=
    PI.AprimeInfT.secondCountable_HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J
  have : LocallyCompactSpace (GI X) :=
    inferInstanceAs (LocallyCompactSpace (HR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J))
  have hd := detNZ_holds X u' ψ hT μinf νinf fibInf hP
  have horb : MulAction.orbit (GI X) (Y0 X u') = FbI X u' hT := by
    apply Set.Subset.antisymm
    · rintro _ ⟨g, rfl⟩; exact orbM_mem X u' hT hd g
    · intro y hy
      obtain ⟨g, hg⟩ := hW X u' ψ hT μinf νinf fibInf hP hy
      exact ⟨g, hg⟩
  have hcl : IsClosed (MulAction.orbit (GI X) (Y0 X u')) := horb ▸ fbI_closed X u' hT hd
  have : LocallyCompactSpace (MulAction.orbit (GI X) (Y0 X u')) :=
    hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hjoint : Continuous (fun p : GI X × TupI X => p.1 • p.2) := by
    refine continuous_pi fun a => ?_
    change Continuous fun p : GI X × TupI X =>
      ((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J p.1 : GL (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
        Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)).mulVec (p.2 a)
    exact ((MassDataMassesW.SplitW.continuous_matHA X.B.I.cm.sig X.B.I.J (Ainf X.B.I.F)).comp
      continuous_fst).matrix_mulVec ((continuous_apply a).comp continuous_snd)
  have : ContinuousSMul (GI X) (MulAction.orbit (GI X) (Y0 X u')) :=
    ⟨continuous_induced_rng.2 (hjoint.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))⟩
  have y0O : Y0 X u' ∈ MulAction.orbit (GI X) (Y0 X u') := MulAction.mem_orbit_self _
  have hopen : IsOpenMap (fun g : GI X => g • (⟨Y0 X u', y0O⟩ : MulAction.orbit (GI X) (Y0 X u'))) :=
    isOpenMap_smul_of_sigmaCompact _
  have hHc : IsCompact (Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u') : Set (GI X)) := by
    have : CompactSpace (Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u')) := hH X u'
    have h := isCompact_range (continuous_subtype_val :
      Continuous (Subtype.val : Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u') → GI X))
    rwa [Subtype.range_coe] at h
  obtain ⟨V, hVc, hV1⟩ := exists_compact_mem_nhds (1 : GI X)
  let U : GI X → Set (MulAction.orbit (GI X) (Y0 X u')) := fun g =>
    (fun h : GI X => h • (⟨Y0 X u', y0O⟩ : MulAction.orbit (GI X) (Y0 X u'))) '' ((fun h => h * g) '' interior V)
  have hUo : ∀ g, IsOpen (U g) := fun g => hopen _ ((isOpenMap_mul_right g) _ isOpen_interior)
  have hKO : IsCompact (Subtype.val ⁻¹' K : Set (MulAction.orbit (GI X) (Y0 X u'))) :=
    hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have hcov : (Subtype.val ⁻¹' K : Set (MulAction.orbit (GI X) (Y0 X u'))) ⊆ ⋃ g, U g := by
    intro y _
    obtain ⟨g, hg⟩ := y.2
    refine Set.mem_iUnion.2 ⟨g, 1 * g, ⟨1, mem_interior_iff_mem_nhds.2 hV1, rfl⟩, ?_⟩
    apply Subtype.ext
    show (1 * g) • Y0 X u' = y.1
    rw [one_mul]; exact hg
  obtain ⟨t, ht⟩ := hKO.elim_finite_subcover U hUo hcov
  refine ⟨⋃ g ∈ t, (fun p : GI X × GI X => p.1 * g * p.2) ''
      (V ×ˢ (Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u') : Set (GI X))),
    t.isCompact_biUnion fun g _ => (hVc.prod hHc).image ((continuous_fst.mul continuous_const).mul continuous_snd),
    fun g hg => ?_⟩
  have hy : (⟨g • Y0 X u', ⟨g, rfl⟩⟩ : MulAction.orbit (GI X) (Y0 X u')) ∈
      (Subtype.val ⁻¹' K : Set (MulAction.orbit (GI X) (Y0 X u'))) := hg
  obtain ⟨g', hg't, hyU⟩ := Set.mem_iUnion₂.1 (ht hy)
  obtain ⟨_, ⟨v, hv, rfl⟩, hvg⟩ := hyU
  have hvg' : (v * g') • Y0 X u' = g • Y0 X u' := congrArg Subtype.val hvg
  refine Set.mem_iUnion₂.2 ⟨g', hg't, (v, (v * g')⁻¹ * g), ⟨interior_subset hv, ?_⟩, ?_⟩
  · show ((v * g')⁻¹ * g) ∈ Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u')
    rw [mem_H_iff]
    change ((v * g')⁻¹ * g) • Y0 X u' = Y0 X u'
    rw [mul_smul, ← hvg', ← mul_smul, inv_mul_cancel, one_smul]
  · exact mul_inv_cancel_left (v * g') g

theorem constTest_of_polar_witt (hP : PolarLoc) (hW : WittInf) (hH : MassDataMassesW.HinfCompact) (hI : InvNbhd) :
    ConstTest :=
  constTest_of_polar_one hP (properOne_of hW hH) hI

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.RmulFactsHolds
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem rmulFacts_holds : RmulFacts := by
  intro D X
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  haveI : BorelSpace (TupI X) :=
    PI.AprimeInfT.borelSpace_tup (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F) (D.R.rS + 1 + D.R.rS)
  have hcont : ∀ a : MfI X, Continuous (rmulT X a) := by
    intro a
    unfold rmulT
    refine continuous_pi fun b => continuous_pi fun i => ?_
    exact continuous_finset_sum _ fun c _ => continuous_const.mul ((continuous_apply i).comp (continuous_apply c))
  refine ⟨fun a => (hcont a).measurable, ?_, ?_, ?_, ?_, ?_, fun K hK => hK.isClosed.measurableSet, hcont⟩
  · intro a b Y
    funext b' i
    simp only [rmulT, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    ring
  · intro g a Y
    funext b i
    show ((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g : GL _ _) : Matrix _ _ _).mulVec (rmulT X a Y b) i =
      ∑ c, a c b * ((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g : GL _ _) : Matrix _ _ _).mulVec (Y c) i
    simp only [rmulT, Matrix.mulVec, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    ring
  · intro a Y
    exact sq_gramR_rmul (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J a Y
  · intro a b
    simp only [cTI, Matrix.map_mul, Matrix.transpose_mul]
  · simp only [cTI, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]

end PI.AprimeInfW
end
end

