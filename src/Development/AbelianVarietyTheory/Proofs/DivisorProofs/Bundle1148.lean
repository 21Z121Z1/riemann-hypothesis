import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1023
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1075
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1092
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1100
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1108
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1112
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1111
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetGaussianEntireOriginGridFrames
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankDdREqOfEquiv
section
open NumberField GlobalTheory.ExpFrame Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N ReciprocityTheory.Gal Formalism.ConjugateSelfDual Polynomial

open Formalism.WeaklyAdmissibleFiltrations Module

noncomputable section

namespace GlobalTheory.ConjCrys

section DdR

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {ρ : Representation LL G V} {ρ' : Representation LL G V'}

theorem ddR_map (f : V →ₗ[LL] V') (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) :
    ∀ x ∈ DdR PD ρ, GlobalTheory.HTW.SumJumps.ext1 Qp BdR f x ∈ DdR PD ρ' := by
  intro x hx
  simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hx ⊢
  intro g
  have := hx g
  unfold actVdR at this ⊢
  rw [GlobalTheory.HTW.SumJumps.ext1_comm f (ρ g) (ρ' g) (hf g), this]

theorem finrank_ddR_eq_of_equiv (e : V ≃ₗ[LL] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v)) :
    finrank LL (DdR PD ρ) = finrank LL (DdR PD ρ') :=
  GlobalTheory.HTW.Rec.finrank_eq_of_equiv_tensor e _ _ (ddR_map PD e.toLinearMap he)
    (ddR_map PD e.symm.toLinearMap (GlobalTheory.HTW.Rec.symm_equivariant e he))

end DdR

section Matrix

theorem mapRep_conj {Γ : Type} [Group Γ] {R S : Type} [CommRing R] [CommRing S] {a : ℕ} (f : R →+* S)
    (M : GL (Fin a) R) (ρ : Γ →* GL (Fin a) R) :
    mapRep f ((MulAut.conj M).toMonoidHom.comp ρ) =
      (MulAut.conj (Units.map (f.mapMatrix : Matrix (Fin a) (Fin a) R →+* Matrix (Fin a) (Fin a) S).toMonoidHom M)).toMonoidHom.comp
        (mapRep f ρ) := by
  ext g : 1
  simp [mapRep, MulAut.conj_apply, map_mul, map_inv]

variable {l : ℕ} [Fact l.Prime]

def glOf {n : ℕ} (L : FinExt l) (A : GL (Fin n) (Om l))
    (hA : ∀ i j, (A : Matrix (Fin n) (Fin n) (Om l)) i j ∈ L.1 ∧
      ((A⁻¹ : GL (Fin n) (Om l)) : Matrix (Fin n) (Fin n) (Om l)) i j ∈ L.1) : GL (Fin n) ↥L.1 where
  val := Matrix.of fun i j => ⟨_, (hA i j).1⟩
  inv := Matrix.of fun i j => ⟨_, (hA i j).2⟩
  val_inv := by
    apply Matrix.map_injective (f := (algebraMap ↥L.1 (Om l))) (algebraMap ↥L.1 (Om l)).injective
    dsimp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact A.mul_inv
  inv_val := by
    apply Matrix.map_injective (f := (algebraMap ↥L.1 (Om l))) (algebraMap ↥L.1 (Om l)).injective
    dsimp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact A.inv_mul

theorem map_glOf {n : ℕ} (L : FinExt l) (A : GL (Fin n) (Om l))
    (hA : ∀ i j, (A : Matrix (Fin n) (Fin n) (Om l)) i j ∈ L.1 ∧
      ((A⁻¹ : GL (Fin n) (Om l)) : Matrix (Fin n) (Fin n) (Om l)) i j ∈ L.1) :
    Units.map ((algebraMap ↥L.1 (Om l)).mapMatrix :
      Matrix (Fin n) (Fin n) ↥L.1 →+* Matrix (Fin n) (Fin n) (Om l)).toMonoidHom (glOf L A hA) = A := by
  ext i j
  rfl

end Matrix

section Local

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  (Bw : LocBridge l E Ω Gw O) {m : ℕ}

def linOf {L : Type} [Field L] (M : GL (Fin m) L) : (Fin m → L) ≃ₗ[L] (Fin m → L) :=
  LinearEquiv.ofLinear (Matrix.toLin' (M : Matrix (Fin m) (Fin m) L))
    (Matrix.toLin' ((M⁻¹ : GL (Fin m) L) : Matrix (Fin m) (Fin m) L))
    (by rw [← Matrix.toLin'_mul, M.mul_inv, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, M.inv_mul, Matrix.toLin'_one])

theorem linOf_repE (L : FinExt l) (M : GL (Fin m) ↥L.1) (r : ↥Gw →* GL (Fin m) ↥L.1) (g) (v : Fin m → ↥L.1) :
    linOf M (Bw.repE L ((MulAut.conj M⁻¹).toMonoidHom.comp r) g v) = Bw.repE L r g (linOf M v) := by
  simp only [linOf, LocBridge.repE, LinearEquiv.ofLinear_apply, MonoidHom.coe_comp, Function.comp_apply,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Units.coeHom_apply, Matrix.toLin'_apply, inv_inv, Units.val_mul]
  erw [Matrix.toLinAlgEquiv'_apply, Matrix.toLinAlgEquiv'_apply]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, M.mul_inv, Matrix.one_mul]

theorem local_conj (L : FinExt l) (M : GL (Fin m) ↥L.1) (r : ↥Gw →* GL (Fin m) ↥L.1) :
    (Bw.IsCrysE P L r → Bw.IsCrysE P L ((MulAut.conj M⁻¹).toMonoidHom.comp r)) ∧
    (Bw.IsdRE P L r → Bw.IsdRE P L ((MulAut.conj M⁻¹).toMonoidHom.comp r)) ∧
    ∀ τ a, Bw.multE P L ((MulAut.conj M⁻¹).toMonoidHom.comp r) τ a = Bw.multE P L r τ a := by
  have he := linOf_repE Bw L M r
  refine ⟨fun h => GlobalTheory.HTW.Rec.isCrys_of_equiv _ (linOf M) he h, fun h => ?_, fun τ a =>
    GlobalTheory.HTW.Rec.multV_eq_of_equiv _ (linOf M) he τ a⟩
  unfold LocBridge.IsdRE at h ⊢
  rw [finrank_ddR_eq_of_equiv _ (linOf M) he, h]

variable {P Bw}

theorem exists_conj_model {r : ↥Gw →* GL (Fin m) (Om l)} (A : GL (Fin m) (Om l)) (K : FinExt l)
    (hA : ∀ i j, (A : Matrix (Fin m) (Fin m) (Om l)) i j ∈ K.1 ∧
      ((A⁻¹ : GL (Fin m) (Om l)) : Matrix (Fin m) (Fin m) (Om l)) i j ∈ K.1)
    {LL' : FinExt l} {r' : ↥Gw →* GL (Fin m) ↥LL'.1} (hm : GlobalTheory.Pst.IsModel Bw r LL' r') :
    ∃ (h : LL'.1 ≤ (GlobalTheory.Pst.supExt LL' K).1) (M : GL (Fin m) ↥(GlobalTheory.Pst.supExt LL' K).1),
      GlobalTheory.Pst.IsModel Bw ((MulAut.conj A⁻¹).toMonoidHom.comp r) (GlobalTheory.Pst.supExt LL' K)
        ((MulAut.conj M⁻¹).toMonoidHom.comp (mapRep (IntermediateField.inclusion h).toRingHom r')) := by
  have h1 : LL'.1 ≤ (GlobalTheory.Pst.supExt LL' K).1 := le_sup_left
  have h2 : K.1 ≤ (GlobalTheory.Pst.supExt LL' K).1 := le_sup_right
  have hA' : ∀ i j, (A : Matrix (Fin m) (Fin m) (Om l)) i j ∈ (GlobalTheory.Pst.supExt LL' K).1 ∧
      ((A⁻¹ : GL (Fin m) (Om l)) : Matrix (Fin m) (Fin m) (Om l)) i j ∈ (GlobalTheory.Pst.supExt LL' K).1 :=
    fun i j => ⟨h2 (hA i j).1, h2 (hA i j).2⟩
  have hm2 := hm.enlarge h1
  refine ⟨h1, glOf _ A hA', hm2.1, ?_⟩
  rw [mapRep_conj, hm2.2, map_inv, map_glOf]

theorem isCrysAt_conj {r : ↥Gw →* GL (Fin m) (Om l)} (A : GL (Fin m) (Om l)) (K : FinExt l)
    (hA : ∀ i j, (A : Matrix (Fin m) (Fin m) (Om l)) i j ∈ K.1 ∧
      ((A⁻¹ : GL (Fin m) (Om l)) : Matrix (Fin m) (Fin m) (Om l)) i j ∈ K.1)
    (hr : GlobalTheory.Pst.IsCrysAt P Bw r) : GlobalTheory.Pst.IsCrysAt P Bw ((MulAut.conj A⁻¹).toMonoidHom.comp r) := by
  obtain ⟨LL', r', hm, hc⟩ := hr
  obtain ⟨h, M, hM⟩ := exists_conj_model A K hA hm
  exact ⟨_, _, hM, (local_conj P Bw _ M _).1 ((GlobalTheory.Pst.local_ext P Bw h r').1.2 hc)⟩

theorem isJumpsAt_conj {r : ↥Gw →* GL (Fin m) (Om l)} (A : GL (Fin m) (Om l)) (K : FinExt l)
    (hA : ∀ i j, (A : Matrix (Fin m) (Fin m) (Om l)) i j ∈ K.1 ∧
      ((A⁻¹ : GL (Fin m) (Om l)) : Matrix (Fin m) (Fin m) (Om l)) i j ∈ K.1)
    {τ : E →+* Om l} {J : Multiset ℤ}
    (hr : GlobalTheory.Pst.IsJumpsAt P Bw r τ J) : GlobalTheory.Pst.IsJumpsAt P Bw ((MulAut.conj A⁻¹).toMonoidHom.comp r) τ J := by
  obtain ⟨LL', r', hm, hdR, τ', hI, hc⟩ := hr
  obtain ⟨h, M, hM⟩ := exists_conj_model A K hA hm
  obtain ⟨-, hdR2, -, hmult⟩ := GlobalTheory.Pst.local_ext P Bw h r'
  obtain ⟨-, hdR3, hmult3⟩ := local_conj P Bw _ M (mapRep (IntermediateField.inclusion h).toRingHom r')
  refine ⟨_, _, hM, hdR3 (hdR2.2 hdR), (IntermediateField.inclusion h).comp τ', fun x => hI x, fun n => ?_⟩
  rw [hc n, hmult3, hmult]

end Local

end GlobalTheory.ConjCrys

open GlobalTheory.ConjCrys in

theorem GlobalTheory.crysWith_conj : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (r : G E Ω →* GL (Fin n) (PadicAlgCl l)) (A : GL (Fin n) (PadicAlgCl l)) (K : FinExt l) (Jm : (E →+* PadicAlgCl l) → Multiset ℤ), (∀ i j, (A : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ K.1 ∧ ((A⁻¹ : GL (Fin n) (PadicAlgCl l)) : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ K.1) → CrysWith r Jm → CrysWith ((MulAut.conj A⁻¹).toMonoidHom.comp r) Jm := by
  intro E Ω _ _ _ _ _ l _ n r A K Jm hA hr
  obtain ⟨hcont, hloc⟩ := hr
  refine ⟨?_, fun P AI hT w B hB O _ _ _ Bw hInd => ?_⟩
  · change Continuous fun g => A⁻¹ * r g * A⁻¹⁻¹
    exact (continuous_const.mul hcont).mul continuous_const
  · obtain ⟨h1, h2⟩ := hloc P AI hT w B hB O Bw hInd
    have e : ((MulAut.conj A⁻¹).toMonoidHom.comp r).comp (Dec (F := E) B).subtype =
        (MulAut.conj A⁻¹).toMonoidHom.comp (r.comp (Dec (F := E) B).subtype) := MonoidHom.comp_assoc _ _ _
    rw [e]
    refine ⟨isCrysAt_conj (r := r.comp (Dec (F := E) B).subtype) A K hA h1, fun τ LL' τ' hI => ?_⟩
    exact isJumpsAt_conj (r := r.comp (Dec (F := E) B).subtype) A K hA (h2 τ LL' τ' hI)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankSmulMemAdelesFiniteMultipleOfTensorCongru
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend

noncomputable section

namespace GlobalTheory.HeckeExtend.TraceCE

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def trAF : AF F ⊗[F] E →ₗ[AF F] AF F :=
  (Algebra.TensorProduct.rid F (AF F) (AF F)).toLinearMap ∘ₗ (Algebra.trace F E).baseChange (AF F)

theorem trAF_tmul (s : AF F) (e : E) :
    trAF (s ⊗ₜ[F] e) = algebraMap F (AF F) (Algebra.trace F E e) * s := by
  simp [trAF, Algebra.TensorProduct.rid_tmul, Algebra.smul_def]

theorem gen_eq (s : AF F) (o : 𝓞 E) :
    algebraMap (AF F) (AF F ⊗[F] E) s * incAF F E o = s ⊗ₜ[F] (o : E) := by
  show (s ⊗ₜ[F] (1 : E)) * ((1 : AF F) ⊗ₜ[F] (o : E)) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem intF_zero : (0 : AF F) ∈ intF F 1 := ⟨0, fun _ => zero_mem _, by rw [one_smul]; rfl⟩

theorem intF_add {x y : AF F} (hx : x ∈ intF F 1) (hy : y ∈ intF F 1) : x + y ∈ intF F 1 := by
  obtain ⟨c, hc, e⟩ := hx
  obtain ⟨d, hd, e'⟩ := hy
  refine ⟨c + d, fun v => add_mem (hc v) (hd v), ?_⟩
  rw [one_smul] at e e' ⊢
  show x.2 + y.2 = c + d
  rw [e, e']

theorem intF_neg {x : AF F} (hx : x ∈ intF F 1) : -x ∈ intF F 1 := by
  obtain ⟨c, hc, e⟩ := hx
  refine ⟨-c, fun v => neg_mem (hc v), ?_⟩
  rw [one_smul] at e ⊢
  show -x.2 = -c
  rw [e]

theorem intF_algebraMap (t : 𝓞 F) : algebraMap F (AF F) (t : F) ∈ intF F 1 :=
  ⟨algebraMap F (Af F) (t : F), fun v => HeightOneSpectrum.coe_algebraMap_mem (𝓞 F) F v t,
    by rw [one_smul]; rfl⟩

theorem trAF_mem_of_mem_SE {z : AF F ⊗[F] E} (hz : z ∈ SE F E) : trAF z ∈ intF F 1 := by
  induction hz using AddSubgroup.closure_induction with
  | mem g hg =>
    obtain ⟨s, hs, o, rfl⟩ := hg
    rw [gen_eq, trAF_tmul]
    have hi : IsIntegral ℤ (Algebra.trace F E (o : E)) := Algebra.isIntegral_trace o.2
    exact intF_one_mul (intF_algebraMap (⟨_, hi⟩ : 𝓞 F)) hs
  | zero => rw [map_zero]; exact intF_zero
  | add a b _ _ ha hb => rw [map_add]; exact intF_add ha hb
  | neg a _ ha => rw [map_neg]; exact intF_neg ha

theorem trAF_algebraMap (x : AF F) :
    trAF (algebraMap (AF F) (AF F ⊗[F] E) x) = Module.finrank F E • x := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, trAF_tmul]
  have h : Algebra.trace F E 1 = (Module.finrank F E : F) := by
    simpa using Algebra.trace_algebraMap (R := F) (S := E) (1 : F)
  rw [h, map_natCast, nsmul_eq_mul]

theorem finrank_smul_mem_intF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) (x : AF F),
    algebraMap (AF F) (AF F ⊗[F] E) x ∈ CE F E N → Module.finrank F E • x ∈ intF F N := by
  intro F E _ _ _ _ _ N x h
  obtain ⟨s, hs, e⟩ := mem_CE.1 h
  have h1 := trAF_algebraMap (E := E) x
  rw [← e, map_nsmul] at h1
  obtain ⟨c, hc, ec⟩ := trAF_mem_of_mem_SE hs
  refine ⟨c, hc, ?_⟩
  rw [← h1]
  rw [one_smul] at ec
  rw [← ec]
  rfl

end GlobalTheory.HeckeExtend.TraceCE

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedAlgebraExists
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

namespace GlobalTheory.FixedCentraliserReg

theorem fixed_algebra_exists : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β Y : G.Cˣ),
    (minpoly G.F (Y : G.C)).Separable → (minpoly G.F (Y : G.C)).natDegree = G.n →
    ∃ (L : Type) (_ : CommRing L) (_ : IsReduced L) (_ : Algebra ℚ L) (_ : FiniteDimensional ℚ L) (ι : L →ₐ[ℚ] G.C), Function.Injective ι ∧
      ∀ c : G.C, c ∈ Set.range ι ↔ Commute c (Y : G.C) ∧ (β : G.C) * sh G c * ((β⁻¹ : G.Cˣ) : G.C) = c := by
  intro p _ G β Y hsep hdeg
  have hcomm : ∀ a b : G.C, Commute a (Y : G.C) → Commute b (Y : G.C) → Commute a b :=
    fun a b ha hb => GlobalTheory.LKCx.ClsReg.commute_of_commute_of_separable G (Y : G.C) hsep hdeg a b ha hb
  have hshmul : ∀ x y : G.C, sh G (x * y) = sh G y * sh G x := by
    intro x y; simp only [sh, map_mul, MulOpposite.unop_mul]
  have hshadd : ∀ x y : G.C, sh G (x + y) = sh G x + sh G y := by
    intro x y; simp only [sh, map_add, MulOpposite.unop_add]
  have hshalg : ∀ q : ℚ, sh G (algebraMap ℚ G.C q) = algebraMap ℚ G.C q := by
    intro q
    have h := RingHom.congr_fun (RingHom.ext_rat (G.star.comp (algebraMap ℚ G.C)) (algebraMap ℚ G.Cᵐᵒᵖ)) q
    simp only [RingHom.comp_apply, MulOpposite.algebraMap_apply] at h
    simp only [sh, h, MulOpposite.unop_op]
  have hββ : ((β⁻¹ : G.Cˣ) : G.C) * (β : G.C) = 1 := by simp
  let S : Subalgebra ℚ G.C :=
    { carrier := {c | Commute c (Y : G.C) ∧ (β : G.C) * sh G c * ((β⁻¹ : G.Cˣ) : G.C) = c}
      mul_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        refine ⟨ha1.mul_left hb1, ?_⟩
        calc (β : G.C) * sh G (a * b) * ((β⁻¹ : G.Cˣ) : G.C)
            = ((β : G.C) * sh G b * ((β⁻¹ : G.Cˣ) : G.C)) * ((β : G.C) * sh G a * ((β⁻¹ : G.Cˣ) : G.C)) := by
              rw [hshmul]
              simp only [mul_assoc]
              rw [← mul_assoc ((β⁻¹ : G.Cˣ) : G.C) (β : G.C), hββ, one_mul]
          _ = b * a := by rw [ha2, hb2]
          _ = a * b := (hcomm a b ha1 hb1).eq.symm
      add_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        refine ⟨ha1.add_left hb1, ?_⟩
        rw [hshadd, mul_add, add_mul, ha2, hb2]
      algebraMap_mem' := by
        intro q
        refine ⟨Algebra.commutes q _, ?_⟩
        rw [hshalg, ← Algebra.commutes q (β : G.C), mul_assoc, Units.mul_inv, mul_one] }
  letI cr : CommRing S :=
    { (inferInstance : Ring S) with
      mul_comm := fun a b => Subtype.ext (hcomm a b a.2.1 b.2.1).eq }
  have hred : IsReduced S := by
    refine ⟨fun x ⟨k, hk⟩ => Subtype.ext ?_⟩
    have hk' : (x : G.C) ^ k = 0 := by
      have := congrArg Subtype.val hk
      simpa using this
    exact GlobalTheory.LKCx.ClsReg.eq_zero_of_commute_of_pow_eq_zero p G (Y : G.C) hsep hdeg x x.2.1 k hk'
  haveI := G.towerC
  haveI := G.finC
  haveI : FiniteDimensional ℚ G.C := Module.Finite.trans G.F G.C
  have hfd : FiniteDimensional ℚ S :=
    Module.Finite.of_injective (S.val.toLinearMap) Subtype.val_injective
  refine ⟨S, cr, hred, S.algebra, hfd, S.val, Subtype.val_injective, fun c => ?_⟩
  constructor
  · rintro ⟨x, rfl⟩; exact x.2
  · intro h; exact ⟨⟨c, h⟩, rfl⟩

end GlobalTheory.FixedCentraliserReg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagOfDominantPointAsTriangularMatrix
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem val_spMap_pt {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) {K : Type} [Field K]
    (σ : Ω →+* K) (x : Ω) : M.val (spMap σ ≫ M.pt) x = σ x := by
  have hx : x ∈ M.O (genericPoint M.Z) := by rw [RatModel.O_genericPoint]; exact Algebra.mem_top
  have := M.val_spMap_comp σ M.pt (M.pt_specializes _ _) ⟨x, hx⟩
  rw [RatModel.valLoc_eq_val, RatModel.val_pt] at this
  exact this

theorem flag_conv : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ B ∈ E'.S (genericPoint Y.X), ∀ A ∈ E.S (f (genericPoint Y.X)), ∀ (K : Type) [Field K] (ψ₁ ψ₂ : Y.Fn →+* K) (U : Mat m K), spMap ψ₁ ≫ (ratOf Y).pt ≫ f = spMap ψ₂ ≫ (ratOf Y).pt ≫ f → Bears E' φ A (U * (B * (A.map φ)⁻¹).map ψ₁) (spMap ψ₂ ≫ (ratOf Y).pt) → (∀ u : X.Fn, ψ₁ (φ u) = ψ₂ (φ u)) ∧ Par m ⊤ (U * (B.map ψ₁ * (B.map ψ₂)⁻¹)) := by
  intro F _ X Y ι _ m E E' φ f hR B hB A hA K _ ψ₁ ψ₂ U hpt hBe
  have hom : (ratOf Y).pt ≫ f = spMap φ.toRingHom ≫ (ratOf X).pt := hR.hom
  have key : ∀ σ : Y.Fn →+* K, spMap σ ≫ (ratOf Y).pt ≫ f = spMap (σ.comp φ.toRingHom) ≫ (ratOf X).pt := by
    intro σ
    rw [hom]
    show Spec.map _ ≫ Spec.map _ ≫ _ = Spec.map (CommRingCat.ofHom (σ.comp φ.toRingHom)) ≫ _
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    exact (Category.assoc _ _ _).symm
  have h1 : ∀ u : X.Fn, ψ₁ (φ u) = ψ₂ (φ u) := by
    intro u
    have e1 := val_spMap_pt (ratOf X) (ψ₁.comp φ.toRingHom) u
    have e2 := val_spMap_pt (ratOf X) (ψ₂.comp φ.toRingHom) u
    rw [← key, hpt, key] at e1
    exact e1.symm.trans e2
  refine ⟨h1, ?_⟩
  obtain ⟨A', hA', hP⟩ := hBe
  have hgen : (spMap ψ₂ ≫ (ratOf Y).pt) (IsLocalRing.closedPoint K) = genericPoint Y.X :=
    (ratOf Y).pt_apply _
  rw [hgen] at hA'
  have hval : (ratOf Y).val (spMap ψ₂ ≫ (ratOf Y).pt) = ψ₂ := funext (val_spMap_pt (ratOf Y) ψ₂)
  rw [hval] at hP
  have hAd : ∀ τ, (A τ).det ≠ 0 := Fr.det_ne hA
  have hBd : ∀ τ, (B τ).det ≠ 0 := Fr.det_ne hB
  have hA'd : ∀ τ, (A' τ).det ≠ 0 := Fr.det_ne hA'
  set C : Mat m Y.Fn := A.map φ with hC
  have hCd : ∀ τ, (C τ).det ≠ 0 := fun τ => by
    rw [hC]; exact fun h0 => (map_ne_zero φ.toRingHom).2 (hAd τ) ((Mat.det_map A φ.toRingHom τ).symm.trans h0)
  have hCψ : C.map ψ₁ = C.map ψ₂ := by
    funext τ; ext i j; exact h1 (A τ i j)
  have hC2d : ∀ τ, (C.map ψ₂ τ).det ≠ 0 := fun τ => by
    rw [Mat.det_map]; exact (map_ne_zero _).2 (hCd τ)
  have hA'2d : ∀ τ, (A'.map ψ₂ τ).det ≠ 0 := fun τ => by
    rw [Mat.det_map]; exact (map_ne_zero _).2 (hA'd τ)
  have e : U * (B * C⁻¹).map ψ₁ * ((A' * C⁻¹).map ψ₂)⁻¹ = U * B.map ψ₁ * (A'.map ψ₂)⁻¹ := by
    rw [Mat.map_mul, Mat.map_mul, Mat.map_inv, Mat.map_inv, hCψ, Mat.mul_inv_rev, Mat.inv_inv hC2d]
    rw [mul_assoc U, mul_assoc (B.map ψ₁), ← mul_assoc (C.map ψ₂)⁻¹, Mat.inv_mul hC2d, one_mul, ← mul_assoc]
  rw [e] at hP
  have hQ : Par m (⊤ : Subring K) ((A' * B⁻¹).map ψ₂) := by
    have := (Fr.mem_iff hB).1 hA'
    exact this.map ψ₂ (fun _ _ => trivial)
  have := hP.mul hQ
  rw [Mat.map_mul, Mat.map_inv] at this
  have e2 : U * B.map ψ₁ * (A'.map ψ₂)⁻¹ * (A'.map ψ₂ * (B.map ψ₂)⁻¹) = U * (B.map ψ₁ * (B.map ψ₂)⁻¹) := by
    rw [mul_assoc (U * B.map ψ₁), ← mul_assoc (A'.map ψ₂)⁻¹, Mat.inv_mul hA'2d, one_mul, mul_assoc]
  rwa [e2] at this

end GlobalTheory.FlagPush
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionsLieRationalWeightsCommuteStatement
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockActions_lie_rationalWeights_commute : ∀ P Q R S : ℕ, IsLieAct (fockAct1 P Q R S) ∧ IsLieAct (fockAct2 P Q R S) ∧ (∀ v, v ∈ ⨆ μ : Ix P Q → ℚ, wtSub (fockAct1 P Q R S) μ) ∧ (∀ v, v ∈ ⨆ μ : Ix R S → ℚ, wtSub (fockAct2 P Q R S) μ) ∧ ∀ X Y f, fockAct1 P Q R S X (fockAct2 P Q R S Y f) = fockAct2 P Q R S Y (fockAct1 P Q R S X f) := by
  first | exact @GlobalTheory.HoweR.fock_lie_wts_comm | exact GlobalTheory.HoweR.fock_lie_wts_comm | (intros; apply GlobalTheory.HoweR.fock_lie_wts_comm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockFormMinorProductEqProdHookProductsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockForm_minorProduct_eq_prod_hookProducts : ∀ (D : D7) (m n : ℕ) (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ), (∀ τ, p τ + q τ ≤ m) → (∀ τ, p τ ≤ n ∧ q τ ≤ n) → (∀ τ, Antitone (ap τ) ∧ Antitone (am τ)) → Formalism.E.fock (Formalism.IndefR.Datum.delta (D := D) (m := m) (n := n) p q ap am) (Formalism.IndefR.Datum.delta p q ap am) = ∏ τ, ((hookOf (p τ) (ap τ) : ℂ) * (hookOf (q τ) (am τ) : ℂ)) := by
  first | exact @GlobalTheory.LowRowFock.fock_delta | exact GlobalTheory.LowRowFock.fock_delta | (intros; apply GlobalTheory.LowRowFock.fock_delta <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicsSupCoinvariantsEqTopStatement
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockHarmonics_sup_coinvariants_eq_top : ∀ (P Q R S : ℕ) (x : ℂ), Submodule.span ℂ (harm2 P Q R S) ⊔ coinv P Q R S x = ⊤ := by
  first | exact @GlobalTheory.HoweR.span_harm2_sup_coinv_eq_univ | exact GlobalTheory.HoweR.span_harm2_sup_coinv_eq_univ | (intros; apply GlobalTheory.HoweR.span_harm2_sup_coinv_eq_univ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetGaussianEntireOriginGridFramesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockJet_gaussianEntire_origin_gridFrames : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (t : T) (j : ℕ), j + 1 ≤ D.R.m → ∀ (F : WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ) (Θ : Formalism.MainNotions.TaylorLogMetric.VC D (G.pS (.top t j)).rank (G.pT (.top t j)).rank → ℂ), Differentiable ℂ Θ → (∀ w : WO (G.pS (.top t j)) (G.pT (.top t j)), w.map (finPart D) = 0 → F w = Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖((N.frC (.top (j + 1)) τ)⁻¹ * compAt W.θ τ w * N.frC (.top j) τ) a b‖ ^ 2 : ℝ) : ℂ)) * Θ (fun τ => (N.frC (.top (j + 1)) τ)⁻¹ * compAt W.θ τ w * N.frC (.top j) τ)) → ∀ k : FVar D (G.pT (.top t j)).rank (G.pS (.top t j)).rank →₀ ℕ, GlobalTheory.FunObj.fockIn W N.frC (.top t j) F (MvPolynomial.monomial k 1) 0 = (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹) ^ (k.sum fun _ n => n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Θ := by
  first | exact @GlobalTheory.FockJetOrigin.fockIn_gauss_zero | exact GlobalTheory.FockJetOrigin.fockIn_gauss_zero | (intros; apply GlobalTheory.FockJetOrigin.fockIn_gauss_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockMonomialAtOriginGaussianEntireOrthonormal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockPos

theorem fock_monomial_zero_of_on : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), IsStdChar D ψ (-1) → IsInfFam θ → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → ∀ (F : WO S T → ℂ) (Φ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ), Differentiable ℂ Φ → (∀ w : WO S T, w.map (finPart D) = 0 → F w = GlobalTheory.FockPos.gaussO θ frS frT w * Φ (GlobalTheory.FockPos.zCo θ frS frT w)) → ∀ k : FVar D T.rank S.rank →₀ ℕ, pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (GlobalTheory.FockPos.frAt frS) (GlobalTheory.FockPos.frAt frT) F (MvPolynomial.monomial k 1) 0 = (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹) ^ (k.sum fun _ n => n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Φ := by
  intro D ψ θ S T frS frT hψ hθ hS hT F Φ hΦ hF k
  have hS' : ∀ τ, (frAt frS τ)ᴴ * gramAt D S τ * frAt frS τ = 1 := frAt_on frS hS
  have hT' : ∀ τ, (frAt frT τ)ᴴ * gramAt D T τ * frAt frT τ = 1 := frAt_on frT hT
  exact GlobalTheory.FockJetOrigin.fock_monomial_zero θ hS' hT' hψ hθ F Φ hΦ (fun w hw => hF w hw) k

end GlobalTheory.FockPos
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockSecondActionQuadraticIdentityModCoinvariantsStatement
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockSecondAction_quadraticIdentity_mod_coinvariants : ∀ (P Q R S : ℕ) (x : ℂ), ∃ α β : ℂ, ∀ a b f, qop (units (fockAct2 P Q R S)) α β a b f ∈ coinv P Q R S x := by
  first | exact @GlobalTheory.HoweR.SecondQuad.qop_mem_coinv | exact GlobalTheory.HoweR.SecondQuad.qop_mem_coinv | (intros; apply GlobalTheory.HoweR.SecondQuad.qop_mem_coinv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalDegreeDivVolumeUnitaryGroupLogBoundStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalDegree_div_volume_unitaryGroup_log_bound : ∀ (r n : ℕ) (d : ℝ) (lam : Fin r → ℝ), 1 ≤ r → 3 ≤ n → 0 ≤ d → StrictAnti lam → (∀ a b, |lam a - lam b| ≤ d + n + 3) → 0 < ReciprocityTheory.ChartRestriction.DS.volU r ∧ 0 < (∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), |lam a - lam b|) / (∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))) ∧ Real.log ((∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), |lam a - lam b|) / (∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))) / ReciprocityTheory.ChartRestriction.DS.volU r) ≤ 2 + (r : ℝ) ^ 2 * Real.log (2 * Real.sqrt 2 * (r : ℝ) ^ 2 * n * (d + 2)) := by
  first | exact @GlobalTheory.LowRow.formalDeg_div_volU_log_bound | exact GlobalTheory.LowRow.formalDeg_div_volU_log_bound | (intros; apply GlobalTheory.LowRow.formalDeg_div_volU_log_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoeffRingPrimeNotIsUnit
section
open GlobalTheory.ExpFrame

namespace GlobalTheory.ExpFrame

theorem Frame.prime_not_isUnit : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) (N : ℕ) (F : Frame l ι N), F.Ok → ¬ IsUnit ((l : ℕ) : F.O) := by
  intro l _ ι N F hF hu
  obtain ⟨u, hu⟩ := hu.exists_left_inv
  obtain ⟨L, -, hL⟩ := hF.ring.2
  have hmem : F.emb u ∈ Set.range F.emb := ⟨u, rfl⟩
  rw [hL] at hmem
  have h1 : F.emb u * (l : PadicAlgCl l) = 1 := by
    have := congrArg F.emb hu
    rwa [map_mul, map_natCast, map_one] at this
  have hl : ‖(l : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
    have e : (l : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [e, PadicAlgCl.norm_extends, Padic.norm_p]
  have h2 := congrArg norm h1
  rw [norm_mul, norm_one, hl] at h2
  have hlgt : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hlpos : (0 : ℝ) < l := by linarith
  have h3 : ‖F.emb u‖ * (l : ℝ)⁻¹ < 1 := by
    calc ‖F.emb u‖ * (l : ℝ)⁻¹ ≤ 1 * (l : ℝ)⁻¹ := by gcongr; exact hmem.2
      _ = (l : ℝ)⁻¹ := one_mul _
      _ < 1 := inv_lt_one_of_one_lt₀ hlgt
  linarith

end GlobalTheory.ExpFrame
end

