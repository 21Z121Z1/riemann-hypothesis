import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0147
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
import Development.AbelianVarietyTheory.Definitions.Foundations.ContinuousOfMemCcSmooth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0152
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0154
import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentComponentMemFrameStabilizer
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompStab

theorem idem_mul {R : Type} [CommRing R] {n : ℕ} (φ : R) (hφ : φ * φ = φ) (A B : Matrix (Fin n) (Fin n) R)
    (h : A * B = 1) : (φ • A + (1 - φ) • (1 : Matrix (Fin n) (Fin n) R)) * (φ • B + (1 - φ) • 1) = 1 := by
  have h1 : φ * (1 - φ) = 0 := by rw [mul_sub, mul_one, hφ, sub_self]
  have h2 : (1 - φ) * φ = 0 := by rw [mul_comm, h1]
  have h3 : (1 - φ) * (1 - φ) = 1 - φ := by rw [mul_sub, mul_one, h2, sub_zero]
  simp only [add_mul, mul_add, smul_mul_smul_comm, h, h1, h2, h3, hφ, zero_smul, mul_one, add_zero, zero_add]
  rw [← add_smul, add_sub_cancel, one_smul]

theorem map_idem {R T : Type} [CommRing R] [CommRing T] {n : ℕ} (ψ : R →+* T) (f : R)
    (M : Matrix (Fin n) (Fin n) R) :
    (f • M + (1 - f) • (1 : Matrix (Fin n) (Fin n) R)).map ψ = ψ f • M.map ψ + (1 - ψ f) • 1 := by
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, map_add,
    map_mul, map_sub, map_one]
  split_ifs <;> simp

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem comp_mem_St (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (φ : Formalism.L2.Herm.intAf F E) (hφ : φ * φ = φ)
    (x x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hS : x ∈ St β)
    (h : x'.1 = (φ : E ⊗[F] Formalism.L2.Herm.Af F) • x.1 + (1 - (φ : E ⊗[F] Formalism.L2.Herm.Af F)) • 1) : x' ∈ St β := by
  obtain ⟨y, rfl⟩ := hS
  refine ⟨⟨φ • y.1 + (1 - φ) • 1, φ • (y⁻¹).1 + (1 - φ) • 1, idem_mul φ hφ _ _ y.mul_inv,
    idem_mul φ hφ _ _ y.inv_mul⟩, Units.ext ?_⟩
  rw [h]
  show β.1 * (φ • y.1 + (1 - φ) • (1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E))).map
      (Formalism.L2.Herm.intAf F E).subtype * (β⁻¹).1 =
    (φ : E ⊗[F] Formalism.L2.Herm.Af F) • (β.1 * y.1.map (Formalism.L2.Herm.intAf F E).subtype * (β⁻¹).1) + _
  rw [map_idem, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, Units.mul_inv]
  rfl

theorem comm_int {z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E}
    (hz : z ∈ AddSubgroup.closure {y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E |
      ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}) :
    (Algebra.TensorProduct.comm F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) E z : E ⊗[F] Formalism.L2.Herm.Af F) ∈
      Formalism.L2.Herm.intAf F E := by
  refine AddSubgroup.closure_induction (p := fun z _ =>
    (Algebra.TensorProduct.comm F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) E z : E ⊗[F] Formalism.L2.Herm.Af F) ∈
      Formalism.L2.Herm.intAf F E) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨a, ha, x, rfl⟩
    have : (Algebra.TensorProduct.comm F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) E (a ⊗ₜ[F] (x : E)) : E ⊗[F] Formalism.L2.Herm.Af F) =
        ((oToS F E x : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) * ((1 : E) ⊗ₜ[F] a) := by
      rw [oToS_coe, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]; rfl
    rw [this]
    exact Subring.mul_mem _ (oToS F E x).2 (Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩))
  · rw [map_zero]; exact Subring.zero_mem _
  · intro a b _ _ ha hb
    rw [map_add]; exact Subring.add_mem _ ha hb
  · intro a _ ha
    rw [map_neg]; exact Subring.neg_mem _ ha

end General

theorem component_mem_St : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (g g' : GA D V) (f : AE D), f * f = f → finE V g ∈ St β → Formalism.L2.Theta.mt V g' = f • Formalism.L2.Theta.mt V g + (1 - f) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) → finE V g' ∈ St β := by
  intro D V β g g' f hf hg h
  let ψ : AE D →+* Lev.EAf D := (swapAE D).comp (finPart D)
  have hi : ψ f ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    comm_int (GlobalTheory.AdIdem.idempotent_mem_intAE D (finPart D f) (by rw [← RingHom.map_mul, hf]))
  refine comp_mem_St β ⟨ψ f, hi⟩ (Subtype.ext ?_) (finE V g) _ hg ?_
  · show ψ f * ψ f = ψ f
    rw [← RingHom.map_mul, hf]
  · show (Formalism.L2.Theta.mt V g').map ψ = ψ f • (Formalism.L2.Theta.mt V g).map ψ + (1 - ψ f) • 1
    rw [h, map_idem]

end GlobalTheory.CompStab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentTwistedGroupEndomorphism
section
noncomputable section

namespace GlobalTheory.UnitaryIdemCut

section Gen

open Matrix Formalism.UG

variable {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n]

def cutM (b : A) (hb : b * b = b) : Matrix n n A →* Matrix n n A where
  toFun M := b • M + (1 - b) • 1
  map_one' := by rw [← add_smul]; simp
  map_mul' M N := by
    have h1 : b * (1 - b) = 0 := by linear_combination -hb
    have h2 : (1 - b) * b = 0 := by linear_combination -hb
    have h3 : (1 - b) * (1 - b) = 1 - b := by linear_combination hb
    simp only [add_mul, mul_add, smul_mul_smul_comm, hb, h1, h2, h3, zero_smul, add_zero, zero_add, mul_one]

def cutGL (b : A) (hb : b * b = b) : GL n A →* GL n A := Units.map (cutM b hb)

theorem cutGL_val (b : A) (hb : b * b = b) (g : GL n A) :
    (cutGL b hb g).val = b • g.val + (1 - b) • 1 := rfl

theorem map_cut (φ : A →+* B) (b : A) (M : Matrix n n A) :
    (b • M + (1 - b) • (1 : Matrix n n A)).map φ = φ b • M.map φ + (1 - φ b) • (1 : Matrix n n B) := by
  ext i j
  by_cases h : i = j <;> simp [h]

theorem bc_cutGL (φ : A →+* B) (b : A) (hb : b * b = b) (b' : B) (hb' : b' * b' = b') (e : φ b = b')
    (g : GL n A) : bc φ (cutGL b hb g) = cutGL b' hb' (bc φ g) := by
  subst e
  exact Units.ext (map_cut φ b g.val)

theorem bc_cutGL_eq_one (φ : A →+* B) (b : A) (hb : b * b = b) {g : GL n A} (hg : bc φ g = 1) :
    bc φ (cutGL b hb g) = 1 := by
  rw [bc_cutGL φ b hb _ (by rw [← map_mul, hb]) rfl, hg, map_one]

theorem cutGL_conj (b : A) (hb : b * b = b) (β g : GL n A) :
    cutGL b hb (β * g * β⁻¹) = β * cutGL b hb g * β⁻¹ := by
  apply Units.ext
  simp only [cutGL_val, Units.val_mul, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, Units.mul_inv]

theorem cutGL_mem_UJ (σ : A →+* A) (J : Matrix n n A) (b : A) (hb : b * b = b) (hσ : σ b = b) {g : GL n A}
    (hg : g ∈ UJ σ J) : cutGL b hb g ∈ UJ σ J := by
  have hg' : cT σ g.val * J * g.val = J := hg
  show cT σ (b • g.val + (1 - b) • 1) * J * (b • g.val + (1 - b) • 1) = J
  have e : cT σ (b • g.val + (1 - b) • (1 : Matrix n n A)) = b • cT σ g.val + (1 - b) • 1 := by
    unfold cT
    rw [map_cut, hσ, transpose_add, transpose_smul, transpose_smul, transpose_one]
  have h1 : b * (1 - b) = 0 := by linear_combination -hb
  have h2 : (1 - b) * b = 0 := by linear_combination -hb
  have h3 : (1 - b) * (1 - b) = 1 - b := by linear_combination hb
  rw [e]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul, hb, h1, h2, h3, zero_smul, add_zero,
    zero_add, mul_one, one_mul, hg']
  rw [← add_smul]; simp

def cutUJ (σ : A →+* A) (J : Matrix n n A) (b : A) (hb : b * b = b) (hσ : σ b = b) : UJ σ J →* UJ σ J :=
  ((cutGL b hb).comp (UJ σ J).subtype).codRestrict _ fun g => cutGL_mem_UJ σ J b hb hσ g.2

end Gen

section Ad

open NumberField IsDedekindDomain Formalism.UG Formalism.L2.DIV
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem idem_mem_intAd (a : FiniteAdeleRing (𝓞 F) F) (ha : a * a = a) : a ∈ intAd F := by
  intro v
  have h : a v * a v = a v := congrArg (fun x : FiniteAdeleRing (𝓞 F) F => x v) ha
  rcases eq_or_ne (a v) 0 with h0 | h0
  · rw [h0]; exact zero_mem _
  · rw [mul_left_cancel₀ h0 (h.trans (mul_one _).symm)]; exact one_mem _

theorem cutGL_mem_St (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (b : E ⊗[F] Formalism.L2.Herm.Af F) (hb : b * b = b)
    (hi : b ∈ Formalism.L2.Herm.intAf F E) {g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hg : g ∈ St β) :
    cutGL b hb g ∈ St β := by
  obtain ⟨y, rfl⟩ := hg
  refine ⟨cutGL (⟨b, hi⟩ : Formalism.L2.Herm.intAf F E) (Subtype.ext hb) y, ?_⟩
  show β * intGL F E n _ * β⁻¹ = cutGL b hb (β * intGL F E n y * β⁻¹)
  rw [cutGL_conj]
  unfold intGL
  rw [bc_cutGL _ _ _ b hb rfl]

theorem bc_cutGL_mem_St {A : Type} [CommRing A] (φ : A →+* E ⊗[F] Formalism.L2.Herm.Af F)
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (b : A) (hb : b * b = b)
    (hi : φ b ∈ Formalism.L2.Herm.intAf F E) {g : GL (Fin n) A} (hg : bc φ g ∈ St β) :
    bc φ (cutGL b hb g) ∈ St β := by
  have hb' : φ b * φ b = φ b := by rw [← map_mul, hb]
  rw [bc_cutGL φ b hb _ hb' rfl]
  exact cutGL_mem_St β _ hb' hi hg

end Ad

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sigR_algebraMap {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (r : R) : sigR R σ (algebraMap R (R ⊗[F] E) r) = algebraMap R (R ⊗[F] E) r := by
  simp [sigR, Algebra.TensorProduct.algebraMap_apply]

theorem exists_cutHA {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (r : R)
    (hb : algebraMap R (R ⊗[F] E) r * algebraMap R (R ⊗[F] E) r = algebraMap R (R ⊗[F] E) r) :
    ∃ κ : HA R σ J →* HA R σ J, ∀ g, HA.mat R σ J (κ g) = cutGL _ hb (HA.mat R σ J g) :=
  ⟨cutUJ (sigR R σ) (JR R J) _ hb (sigR_algebraMap R σ r), fun _ => rfl⟩

theorem mem_GfC_iff {D : D7} (V : HSp D) (g : GA D V) :
    g ∈ GfC V ↔ Formalism.UG.bc (infPart D) (matHom V g) = 1 := Iff.rfl

theorem finE_eq {D : D7} (V : HSp D) (g : GA D V) : finE V g = Formalism.UG.bc (toEAf D) (matHom V g) :=
  Units.ext (finE_val V g)

theorem exists_cut : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (ε : AF D.host.F), ε * ε = ε → ∃ κ : GA D V →* GA D V, ∀ g, Formalism.L2.Theta.mt V (κ g) = algebraMap (AF D.host.F) (AE D) ε • Formalism.L2.Theta.mt V g + (1 - algebraMap (AF D.host.F) (AE D) ε) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) ∧ (Stab V β g → Stab V β (κ g)) := by
  intro D V β ε hε
  have hb : algebraMap (AF D.host.F) (AE D) ε * algebraMap (AF D.host.F) (AE D) ε = algebraMap (AF D.host.F) (AE D) ε := by
    rw [← map_mul, hε]
  obtain ⟨κ, hκ⟩ := exists_cutHA (AF D.host.F) D.sp.cm.sig V.gram ε hb
  have hκ' : ∀ g, matHom V (κ g) = cutGL _ hb (matHom V g) := hκ
  refine ⟨κ, fun g => ⟨congrArg Units.val (hκ' g), fun h => ⟨?_, ?_⟩⟩⟩
  · have h1 := (mem_GfC_iff V g).1 h.1
    rw [mem_GfC_iff, hκ']
    exact bc_cutGL_eq_one (infPart D) _ hb h1
  · have h1 := h.2
    rw [finE_eq] at h1
    have hi : toEAf D (algebraMap (AF D.host.F) (AE D) ε) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
      Subring.subset_closure (Or.inr ⟨⟨sndA D.host.F ε, idem_mem_intAd _ (by rw [← map_mul, hε])⟩, rfl⟩)
    rw [finE_eq, hκ']
    exact bc_cutGL_mem_St (toEAf D) β _ hb hi h1

end GlobalTheory.UnitaryIdemCut

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InjectiveOfIndep
section
noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.GeoActCompare

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.L2.Pj
  Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.GeometricConstantEquiv (Cusp IsLift IsGeo ReadTwist KeepsIntegral IsIntegralForm ConstEquiv IsKappa GeoActAt)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Model

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem levChi_flag (i : Fin D.R.m) (k : GA D (Wc D i)) : levChi _ (R.βW i) (flagL (R.datWp i R.triv)) k = 1 := by
  simp [levChi, Formalism.L2.DIV.levFn, flagL, withP, LevCh.datWp, datY, LevelP.full]
  first
    | exact subgroupCharExtension_one_apply _ _
    | (unfold Formalism.L2.DIV.ext1; exact dite_eq_right_iff.2 fun _ => rfl)

private theorem wall_apply_mul_eq_levChi_mul_of_mem_levS {i : Fin D.R.m} {σ : D.what₂.LL →+* ℂ} {T : MMap (R.MW i σ)} (hT : T ∈ R.Wall i σ)
    (v : (R.MW i σ).Vec) {k : GA D (Wc D i)} (hk : k ∈ levS _ (R.βW i) (R.datWp i R.triv)) (g : GA D (Wc D i)) :
    T v (g * k) = levChi _ (R.βW i) (R.datWp i R.triv) k * T v g := by
  unfold RealDat.Wall Formalism.IndefR.Mult.Mult at hT
  induction hT using Submodule.span_induction with
  | mem x hx =>
    have hx' : IsMultMap R.θ (R.MW i σ) (levS _ (R.βW i) (R.datWp i R.triv))
        (levChi _ (R.βW i) (R.datWp i R.triv)) x := hx
    exact hx'.lev v k hk g
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [MultilinearMap.add_apply, Pi.add_apply, hx, hy]
    ring
  | smul a x _ hx =>
    simp only [MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, hx]
    ring

theorem hasType_e (he : R.models_HW) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (y : (R.HW i σ).H) (v : (R.MW i σ).Vec) :
    HasType (Wc D i) (R.βW i) (flag1L (R.datWp i R.triv)) ((R.HW i σ).e y v) := by
  have hm : (R.HW i σ).e y ∈ R.Wall i σ := by
    rw [← (he i σ).2.1]
    exact LinearMap.mem_range_self _ y
  intro k hk h
  exact wall_apply_mul_eq_levChi_mul_of_mem_levS R hm v hk h

theorem actW_apply (he : R.models_HW) {i : Fin D.R.m} (σ : D.what₂.LL →+* ℂ) {g : G} {k : GA D (Wc D i)}
    (hk : IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k) (y : (R.HW i σ).H) (v : (R.MW i σ).Vec)
    (x : GA D (Wc D i)) : actW R i σ g ((R.HW i σ).e y) v x = (R.HW i σ).e y v (x * k) := by
  have hs := level_action_spec (hasType_e R he i σ y v) ⟨k, hk⟩ k hk x
  rw [levChi_flag R i k, inv_one, one_mul] at hs
  exact hs

end Model

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

theorem cast_mul {V W : HSp D} (h : V = W) (x y : GA D V) :
    cast (congrArg (GA D) h) (x * y) = cast (congrArg (GA D) h) x * cast (congrArg (GA D) h) y := by
  subst h
  rfl

def ReadModel (i : Fin D.R.m) (ρ : G →* (Cu T κ i →ₗ[T.Q.c.F] Cu T κ i)) : Prop :=
  ∀ σ g f, (R.HW i σ).e (jTop T R κ v₀ i σ (ρ g f)) =
    σ ((chiTop R i g : D.what₂.LLˣ) : D.what₂.LL) • actW R i σ g ((R.HW i σ).e (jTop T R κ v₀ i σ f))

structure Ties : Prop where
  laws : LawsJ T
  model : R.models_HW
  act : R.models_gW
  chi : R.grp_chiW
  vec : ∀ i σ, IsChosenExtremalVector R i σ (v₀ i σ)

variable {T R κ v₀}

end GlobalTheory.GeoActCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralMulEqZeroOfCosetIntegralEqZero
section
open MeasureTheory GlobalTheory.AutomorphicL2Unitary Topology Set Filter
open scoped Pointwise

noncomputable section

namespace GlobalTheory.CosetIntegralZero

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]

def cosetAvg (H : Subgroup G) (ν : Measure H) (ψ : G → ℝ) (g : G) : ℝ :=
  ∫ u : H, ψ ((u : G)⁻¹ * g) ∂ν

theorem cosetAvg_mul [BorelSpace G] [SecondCountableTopology G] (H : Subgroup G) (ν : Measure H) [ν.IsMulLeftInvariant]
    (ψ : G → ℝ) (u : H) (g : G) : cosetAvg H ν ψ ((u : G) * g) = cosetAvg H ν ψ g := by
  unfold cosetAvg
  rw [← integral_mul_left_eq_self (fun v : H => ψ ((v : G)⁻¹ * ((u : G) * g))) u]
  congr 1; ext v
  simp [mul_inv_rev, mul_assoc]

theorem continuous_cosetAvg [LocallyCompactSpace G] [BorelSpace G] (H : Subgroup G) (hH : IsClosed (H : Set G))
    (ν : Measure H) [IsFiniteMeasureOnCompacts ν] {ψ : G → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    Continuous (cosetAvg H ν ψ) := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  obtain ⟨t, t_comp, ht⟩ := exists_compact_mem_nhds x₀
  have hk : IsCompact (((↑) : H → G) ⁻¹' (t • (tsupport ψ)⁻¹)) :=
    hH.isClosedEmbedding_subtypeVal.isCompact_preimage (t_comp.smul_set hψc.inv)
  have A : ContinuousOn (cosetAvg H ν ψ) t := by
    apply continuousOn_integral_of_compact_support hk
    · exact (hψ.comp ((continuous_subtype_val.comp continuous_snd).inv.mul continuous_fst)).continuousOn
    · intro p x hp hx
      contrapose! hx
      refine ⟨p, hp, p⁻¹ * (x : G), ?_, by simp⟩
      simpa only [Set.mem_inv, mul_inv_rev, inv_inv] using subset_tsupport _ hx
  exact A.continuousAt ht

theorem cosetAvg_pos [BorelSpace G] [SecondCountableTopology G] (H : Subgroup G) (hH : IsClosed (H : Set G))
    (ν : Measure H) [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν] {ψ : G → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x) {g : G} (hg : ψ g ≠ 0) : 0 < cosetAvg H ν ψ g := by
  have C : Continuous (fun u : H => ψ ((u : G)⁻¹ * g)) := by fun_prop
  apply (integral_pos_iff_support_of_nonneg (fun u => hψ0 _) ?_).2
  · apply C.isOpen_support.measure_pos ν
    exact ⟨1, by simpa using hg⟩
  · apply C.integrable_of_hasCompactSupport
    refine HasCompactSupport.intro (hH.isClosedEmbedding_subtypeVal.isCompact_preimage
      ((show IsCompact (tsupport ψ) from hψc).image (f := fun k => g * k⁻¹) (by fun_prop))) ?_
    intro u hu
    by_contra h
    exact hu ⟨(u : G)⁻¹ * g, subset_tsupport _ h, by simp⟩

theorem integrable_prod_of_bound [LocallyCompactSpace G] [T2Space G] [BorelSpace G] [SecondCountableTopology G]
    (H : Subgroup G) (ν : Measure H) [IsFiniteMeasureOnCompacts ν] [SFinite ν]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [SFinite μ]
    {P : H × G → ℂ} (hP : Continuous P) {C : ℝ} (hC : ∀ z, ‖P z‖ ≤ C) {S : Set H} {M : Set G}
    (hS : IsCompact S) (hM : IsCompact M) (hPS : ∀ u g, P (u, g) ≠ 0 → u ∈ S ∧ g ∈ M)
    {w : G → ℂ} (hw : LocallyIntegrable w μ) :
    Integrable (fun z : H × G => P z * w z.2) (ν.prod μ) := by
  have hSi : Integrable (S.indicator (fun _ => (1:ℝ))) ν :=
    (integrableOn_const hS.measure_ne_top).integrable_indicator hS.measurableSet
  have hMi : Integrable (fun g => C * ‖M.indicator w g‖) μ :=
    ((hw.integrableOn_isCompact hM).integrable_indicator hM.measurableSet).norm.const_mul C
  refine (hSi.mul_prod hMi).mono' ?_ (Eventually.of_forall fun z => ?_)
  · exact hP.aestronglyMeasurable.mul hw.aestronglyMeasurable.comp_snd
  · obtain ⟨u, g⟩ := z
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (u, g))
    by_cases h : P (u, g) = 0
    · simp only [h, zero_mul, norm_zero]
      exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (mul_nonneg hC0 (norm_nonneg _))
    · obtain ⟨hu, hg⟩ := hPS u g h
      simp only [Set.indicator_of_mem hu, Set.indicator_of_mem hg, one_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)

theorem integral_cosetAvg_mul_eq [LocallyCompactSpace G] [T2Space G] [BorelSpace G] [SecondCountableTopology G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) (ν : Measure H) [ν.IsHaarMeasure] [SFinite ν]
    (μ : Measure G) [μ.IsHaarMeasure] [SFinite μ] {ψ : G → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hψ1 : ∀ g, |ψ g| ≤ 1) {F w : G → ℂ} (hF : Continuous F) (hFc : HasCompactSupport F)
    (hw : LocallyIntegrable w μ) (hinv : ∀ u ∈ H, (fun g => w (u * g)) =ᵐ[μ] w) :
    ∫ g, (cosetAvg H ν ψ g : ℂ) * F g * w g ∂μ = ∫ g, (ψ g : ℂ) * w g * ∫ u : H, F ((u : G) * g) ∂ν ∂μ := by
  obtain ⟨C, hC⟩ := hF.bounded_above_of_compact_support hFc
  have hS : IsCompact (((↑) : H → G) ⁻¹' ((fun p : G × G => p.1 * p.2⁻¹) '' (tsupport F ×ˢ tsupport ψ))) :=
    hH.isClosedEmbedding_subtypeVal.isCompact_preimage
      (((show IsCompact (tsupport F) from hFc).prod (show IsCompact (tsupport ψ) from hψc)).image (by fun_prop))
  have I1 : Integrable (fun z : H × G => ((ψ ((z.1 : G)⁻¹ * z.2) : ℂ) * F z.2) * w z.2) (ν.prod μ) := by
    refine integrable_prod_of_bound H ν μ (by fun_prop) (C := C) ?_ hS (show IsCompact (tsupport F) from hFc) ?_ hw
    · intro z
      rw [norm_mul]
      calc _ ≤ 1 * C := mul_le_mul (by simpa using hψ1 _) (hC _) (norm_nonneg _) zero_le_one
        _ = C := one_mul C
    · intro u g h
      have h1 : ψ ((u : G)⁻¹ * g) ≠ 0 := fun h' => h (by simp [h'])
      have h2 : F g ≠ 0 := fun h' => h (by simp [h'])
      exact ⟨⟨(g, (u : G)⁻¹ * g), ⟨subset_tsupport _ h2, subset_tsupport _ h1⟩, by simp⟩, subset_tsupport _ h2⟩
  have I2 : Integrable (fun z : H × G => ((ψ z.2 : ℂ) * F ((z.1 : G) * z.2)) * w z.2) (ν.prod μ) := by
    refine integrable_prod_of_bound H ν μ (by fun_prop) (C := C) ?_ hS (show IsCompact (tsupport ψ) from hψc) ?_ hw
    · intro z
      rw [norm_mul]
      calc _ ≤ 1 * C := mul_le_mul (by simpa using hψ1 _) (hC _) (norm_nonneg _) zero_le_one
        _ = C := one_mul C
    · intro u g h
      have h1 : ψ g ≠ 0 := fun h' => h (by simp [h'])
      have h2 : F ((u : G) * g) ≠ 0 := fun h' => h (by simp [h'])
      exact ⟨⟨((u : G) * g, g), ⟨subset_tsupport _ h2, subset_tsupport _ h1⟩, by simp⟩, subset_tsupport _ h1⟩
  calc ∫ g, (cosetAvg H ν ψ g : ℂ) * F g * w g ∂μ
      = ∫ g, ∫ u : H, (ψ ((u : G)⁻¹ * g) : ℂ) * F g * w g ∂ν ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun g => ?_)
        simp only [cosetAvg, mul_assoc]
        rw [integral_mul_const, integral_complex_ofReal]
    _ = ∫ u : H, ∫ g, (ψ ((u : G)⁻¹ * g) : ℂ) * F g * w g ∂μ ∂ν :=
        (integral_integral_swap (f := fun (u : H) (g : G) => (ψ ((u : G)⁻¹ * g) : ℂ) * F g * w g) I1).symm
    _ = ∫ u : H, ∫ g, (ψ g : ℂ) * F ((u : G) * g) * w g ∂μ ∂ν := by
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        dsimp only
        conv_lhs => rw [← integral_mul_left_eq_self _ (u : G)]
        refine integral_congr_ae ?_
        filter_upwards [hinv u u.2] with g hg
        simp only [inv_mul_cancel_left, hg]
    _ = ∫ g, ∫ u : H, (ψ g : ℂ) * F ((u : G) * g) * w g ∂ν ∂μ :=
        integral_integral_swap (f := fun (u : H) (g : G) => (ψ g : ℂ) * F ((u : G) * g) * w g) I2
    _ = ∫ g, (ψ g : ℂ) * w g * ∫ u : H, F ((u : G) * g) ∂ν ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun g => ?_)
        dsimp only
        rw [← integral_const_mul]
        congr 1; ext u; ring

theorem integral_mul_eq_zero_of_coset_integral_eq_zero : ∀ (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] (H : Subgroup G), IsClosed (H : Set G) → ∀ (ν : Measure H) [ν.IsHaarMeasure]
    (μ : Measure G) [μ.IsHaarMeasure] (f w : G → ℂ), Continuous f → HasCompactSupport f →
    LocallyIntegrable w μ → (∀ u ∈ H, (fun g => w (u * g)) =ᵐ[μ] w) →
    (∀ g, ∫ u : H, f (u * g) ∂ν = 0) → ∫ g, f g * w g ∂μ = 0 := by
  intro G _ _ _ _ _ _ _ _ H hH ν _ μ _ f w hf hfc hw hinv hzero
  haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨ψ₀, hψ1, -, hψc, hψ01⟩ := exists_continuous_one_zero_of_isCompact
    (show IsCompact (tsupport f) from hfc) isClosed_empty (Set.disjoint_empty _)
  have hJc : Continuous (cosetAvg H ν ψ₀) := continuous_cosetAvg H hH ν ψ₀.continuous hψc
  have hJpos : ∀ g ∈ tsupport f, 0 < cosetAvg H ν ψ₀ g := fun g hg =>
    cosetAvg_pos H hH ν ψ₀.continuous hψc (fun x => (hψ01 x).1) (by rw [hψ1 hg]; simp)
  set F : G → ℂ := fun g => f g / (cosetAvg H ν ψ₀ g : ℂ) with hFdef
  have hF : Continuous F := by
    refine continuous_iff_continuousAt.2 fun g => ?_
    by_cases hg : g ∈ tsupport f
    · exact hf.continuousAt.div (Complex.continuous_ofReal.comp hJc).continuousAt
        (by exact_mod_cast (hJpos g hg).ne')
    · have : F =ᶠ[𝓝 g] fun _ => 0 := by
        filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hg] with x hx
        simp [hFdef, image_eq_zero_of_notMem_tsupport hx]
      exact continuousAt_const.congr this.symm
  have hFc : HasCompactSupport F :=
    hfc.mono fun g hg h => hg (by simp [hFdef, h])
  have hFJ : ∀ g, (cosetAvg H ν ψ₀ g : ℂ) * F g * w g = f g * w g := by
    intro g
    by_cases h : f g = 0
    · simp [hFdef, h]
    · have hJ : (cosetAvg H ν ψ₀ g : ℂ) ≠ 0 := by exact_mod_cast (hJpos g (subset_tsupport _ h)).ne'
      rw [hFdef, mul_div_cancel₀ _ hJ]
  have hFH : ∀ g, ∫ u : H, F ((u : G) * g) ∂ν = 0 := by
    intro g
    simp only [hFdef, cosetAvg_mul H ν ψ₀ _ g]
    rw [integral_div, hzero g, zero_div]
  have key := integral_cosetAvg_mul_eq H hH ν μ ψ₀.continuous hψc
    (fun g => by rw [abs_le]; constructor <;> linarith [(hψ01 g).1, (hψ01 g).2]) hF hFc hw hinv
  simp only [hFJ, hFH, mul_zero, integral_zero] at key
  exact key

end GlobalTheory.CosetIntegralZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenEmbeddingFiniteAdeleOfSPartAndIntegralPartStatement
section
open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpenEmbedding_finiteAdeleOfSPartAndIntegralPart : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))), IsOpenEmbedding (jS F S) := by
  first | exact @GlobalTheory.ModuLR.isOpenEmbedding_jS | exact GlobalTheory.ModuLR.isOpenEmbedding_jS | (intros; apply GlobalTheory.ModuLR.isOpenEmbedding_jS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralEqZeroOfNormalisedCosetIntegralsStatement
section
open MeasureTheory Set GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotientIntegral_eq_zero_of_normalised_coset_integrals : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (T N : Subgroup H), IsClosed (T : Set H) → IsClosed (N : Set H) → IsMulCommutative T → (∀ t ∈ T, ∀ n ∈ N, t * n * t⁻¹ ∈ N) → Topology.IsClosedEmbedding (fun p : N × T => (p.1 : H) * p.2) → ∀ (dh : Measure H) [dh.IsHaarMeasure] (dt : Measure T) [dt.IsHaarMeasure] (dn : Measure N) [dn.IsHaarMeasure] [dn.IsMulRightInvariant] (φ : H → ℂ), Measurable φ → LeftInv T φ → Integrable (descend T φ) (quotMeas T dt dh) → (∀ x, ∫ n : N, φ (n * x) ∂dn = 0) → quotInt T dt dh φ = 0 := by
  first | exact @GlobalTheory.Orb.quotInt_eq_zero_of_integral_coset_eq_zero | exact GlobalTheory.Orb.quotInt_eq_zero_of_integral_coset_eq_zero | (intros; apply GlobalTheory.Orb.quotInt_eq_zero_of_integral_coset_eq_zero <;> assumption)
end

