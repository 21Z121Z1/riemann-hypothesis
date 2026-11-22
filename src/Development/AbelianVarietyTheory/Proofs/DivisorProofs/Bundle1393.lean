import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0944
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1347
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0932
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0132
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0571
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1241
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1211
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1337
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1323
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1335
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1289
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1324
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1353

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameOnBaseCharacter
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MuLift

section Ring

theorem orth_mul {R : Type} [CommRing R] {e f : R} (he : e * e = e) (hf : f * f = f) (hef : e * f = 0)
    {p q p' q' : R} (hp : p * p' = 1) (hq : q * q' = 1) :
    (e * p + f * q + (1 - e - f)) * (e * p' + f * q' + (1 - e - f)) = 1 := by
  have eg : e * (1 - e - f) = 0 := by linear_combination -he - hef
  have fg : f * (1 - e - f) = 0 := by linear_combination -hf - hef
  have gg : (1 - e - f) * (1 - e - f) = 1 - e - f := by linear_combination -eg - fg
  linear_combination (p * p') * he + (q * q') * hf + (p * q' + q * p') * hef + (p + p') * eg + (q + q') * fg + gg +
    e * hp + f * hq

theorem exists_root {R A : Type} [CommRing R] [CommRing A] (c : R →+* R) (hc : ∀ z, c (c z) = z) (S : Subring R)
    (hS : ∀ z ∈ S, c z ∈ S) (p : R →+* A) {e d : R} (he : e * e = e) (hef : e * c e = 0) (heS : e ∈ S)
    (hpe : p e = 0) (hpf : p (c e) = 0) (x : Rˣ) (hx : (x : R) = d * c x) (h1 : p x = 1) (h2 : (x : R) ∈ S)
    (h3 : ((x⁻¹ : Rˣ) : R) ∈ S) :
    ∃ y : Rˣ, (y : R) = d * c y ∧ p y = 1 ∧ (y : R) ∈ S ∧ ((y⁻¹ : Rˣ) : R) ∈ S ∧ c e * y = c e ∧ e * y = e * d := by
  have hf : c e * c e = c e := by rw [← map_mul, he]
  have hxx : ((x⁻¹ : Rˣ) : R) * x = 1 := x.inv_mul
  have hcx : c ((x⁻¹ : Rˣ) : R) * c x = 1 := by rw [← map_mul, hxx, map_one]
  have hw := orth_mul he hf hef hcx hxx
  let w : Rˣ := ⟨_, _, hw, (mul_comm _ _).trans hw⟩
  have hw1 : (w : R) = e * c ((x⁻¹ : Rˣ) : R) + c e * ((x⁻¹ : Rˣ) : R) + (1 - e - c e) := rfl
  have hw2 : ((w⁻¹ : Rˣ) : R) = e * c (x : R) + c e * (x : R) + (1 - e - c e) := rfl
  have hcw : c w = w := by
    rw [hw1]
    simp only [map_add, map_mul, map_sub, map_one, hc]
    ring
  have hm : ∀ a ∈ S, e * c a + c e * a + (1 - e - c e) ∈ S := fun a ha =>
    add_mem (add_mem (mul_mem heS (hS _ ha)) (mul_mem (hS _ heS) ha)) (sub_mem (sub_mem (one_mem _) heS) (hS _ heS))
  refine ⟨x * w, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Units.val_mul, map_mul, hcw, ← mul_assoc, ← hx]
  · rw [Units.val_mul, hw1]
    simp only [map_add, map_mul, map_sub, map_one, h1, hpe, hpf]
    ring
  · rw [Units.val_mul, hw1]
    exact mul_mem h2 (hm _ h3)
  · rw [mul_inv, Units.val_mul, hw2]
    exact mul_mem h3 (hm _ h2)
  · rw [Units.val_mul, hw1]
    linear_combination (x * c ((x⁻¹ : Rˣ) : R) - x) * hef + (x * ((x⁻¹ : Rˣ) : R) - x) * hf + c e * hxx
  · rw [Units.val_mul, hw1]
    linear_combination (x * c ((x⁻¹ : Rˣ) : R) - x) * he + (x * ((x⁻¹ : Rˣ) : R) - x) * hef +
      e * c ((x⁻¹ : Rˣ) : R) * hx + e * d * hcx

end Ring

section General

open NumberField Formalism.L2.DIV
open scoped TensorProduct

theorem det_restricted_block {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) (h : n = r) (g : GL (Fin n) κ) :
    Matrix.GeneralLinearGroup.det (upperLeftBlock hr g) = Matrix.GeneralLinearGroup.det g := by
  subst h
  have hg : g ∈ blockTri (blk2 n) := fun i j hij => by
    simp [blk2] at hij
  congr 1
  exact Units.ext (upper_block_val_submatrix hr hg)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem resS_eq_gen (PP : Pl E) {a x y : E ⊗[F] Formalism.L2.Herm.Af F} (ha : a ∈ Formalism.L2.Herm.intAf F E)
    (hx : x ∈ Formalism.L2.Herm.intAf F E) (hy : y ∈ Formalism.L2.Herm.intAf F E) (h1 : resS F PP ⟨a, ha⟩ = 1)
    (h : a * x = a * y) : resS F PP ⟨x, hx⟩ = resS F PP ⟨y, hy⟩ := by
  have e : (⟨a, ha⟩ : Formalism.L2.Herm.intAf F E) * ⟨x, hx⟩ = ⟨a, ha⟩ * ⟨y, hy⟩ := Subtype.ext h
  have := congrArg (resS F PP) e
  rwa [map_mul, map_mul, h1, one_mul, one_mul] at this

theorem det_int_gen {n : ℕ} {β g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hg : g ∈ St β)
    {d : E ⊗[F] Formalism.L2.Herm.Af F} (hd : d = g.val.det) :
    ∃ h : d ∈ Formalism.L2.Herm.intAf F E, ∀ PP : Pl E,
      ((Matrix.GeneralLinearGroup.det (redFn β PP g) : (kP PP)ˣ) : kP PP) = resS F PP ⟨d, h⟩ := by
  obtain ⟨y, rfl⟩ := hg
  have h3 : d = (y.val.det : Formalism.L2.Herm.intAf F E) := by
    rw [hd]
    change (β * intGL _ _ _ y * β⁻¹).val.det = _
    rw [Units.val_mul, Units.val_mul, Matrix.det_units_conj]
    exact ((Formalism.L2.Herm.intAf F E).subtype.map_det y.val).symm
  subst h3
  refine ⟨y.val.det.2, fun PP => ?_⟩
  rw [redFn_frGL]
  exact ((resS F PP).map_det y.val).symm

end General

section Adelic

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
open Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj GlobalTheory.StepLaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem exists_idemSum (P : Finset (Pl D.host.E)) (h : ∀ Q ∈ P, ∀ Q' ∈ P, ¬ IsConjPl Q Q') :
    ∃ e : AE D, IsIdemSum e P :=
  GlobalTheory.GridIdem.exists_isIdemSum P (fun Q hQ => GlobalTheory.ParahoricLift.exists_isIdemAt (h Q hQ Q hQ))
    fun Q hQ Q' hQ' e => (GlobalTheory.IdemSupport.eq_or_eq_cP e).resolve_right fun e' =>
      h Q' hQ' Q hQ ((GlobalTheory.IdemSupport.isConjPl_iff Q' Q).2 e')

theorem cA_cA (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rfl
  | tmul a x => exact congrArg (a ⊗ₜ[D.host.F] ·) (star_star x)
  | add a b ha hb => rw [RingHom.map_add, RingHom.map_add, ha, hb]

set_option maxHeartbeats 1000000 in

theorem mu_eq_prod {V : HSp D} {χ : (AE D)ˣ →* Circle} {mu : GA D V → ℂ} (hV : MuVal V χ mu) {e : AE D}
    {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) {c : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} (hχ : TameOn χ e P c)
    {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)} {k : GA D V} (hf : k ∈ GfC V) (hk : finE V k ∈ St β) :
    mu k = ∏ PP ∈ P, ((c PP (Matrix.GeneralLinearGroup.det (redFn β PP (finE V k))) : ℂˣ) : ℂ) := by
  obtain ⟨hd, hr⟩ : ∃ h : toEAf D (Formalism.L2.Theta.mt V k).det ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
      ∀ PP : Pl D.host.E, ((Matrix.GeneralLinearGroup.det (redFn β PP (finE V k)) : (kP PP)ˣ) : kP PP) =
        resS D.host.F PP ⟨_, h⟩ := det_int_gen hk ((toEAf D).map_det _)
  have e5 : (finHom V k).1.det = finPart D (Formalism.L2.Theta.mt V k).det := ((finPart D).map_det _).symm
  obtain ⟨x, hx, hx1, hx2, hx3⟩ := GlobalTheory.GeoLevel.LiftChar.exists_finUnit_root V k hf
    (e5 ▸ GlobalTheory.PlaceDatum.finPart_mem_of_toEAf hd)
  obtain ⟨hei, her⟩ := GlobalTheory.TameProd.resS_idemSum he
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum he
  obtain ⟨y, hy, hy1, hy2, hy3, hy4, hy5⟩ := exists_root (cA D) cA_cA
    ((Formalism.L2.Herm.intAf D.host.F D.host.E).comap (toEAf D))
    (fun z hz => GlobalTheory.IdemRes.toEAf_mem_of_finPart
      (GlobalTheory.IdemSupport.finPart_cA_mem (GlobalTheory.PlaceDatum.finPart_mem_of_toEAf hz)))
    (infPart D) (d := (Formalism.L2.Theta.mt V k).det) (GlobalTheory.PlaceDatum.idemSum_mul_self he) he.2 hei hinf
    (GlobalTheory.PlaceDatum.infPart_cA hinf) x hx hx1 (GlobalTheory.IdemRes.toEAf_mem_of_finPart hx2)
    (GlobalTheory.IdemRes.toEAf_mem_of_finPart hx3)
  rw [hV.2 k y hy]
  refine hχ y hy1 hy2 hy3 hy4 (fun PP => Matrix.GeneralLinearGroup.det (redFn β PP (finE V k))) fun PP hP => ?_
  refine (hr PP).trans (resS_eq_gen PP hei hd hy2 (her PP hP) ?_)
  rw [← RingHom.map_mul, ← hy5, RingHom.map_mul]

theorem tame_on_base_character {T0 : Type} {L : LevCh D T0} {μ0 : T0} (hL : L.Is μ0) (j : Fin D.R.m) {e : AE D}
    (he : IsIdemSum e L.Pg) : TameOn (L.mu0 ((j : ℕ) + 1)) e L.Pg fun PP => (L.chi ((j : ℕ) + 1) PP)⁻¹ := by
  have hM := L.C.isMu0 j
  refine GlobalTheory.TameProd.tameOn_of_tame D _ (L.C.mu0 j) e L.Pg _ (hL.mu0 j) hM.tame he ?_ (hL.chi j)
  intro PP h1 h2
  refine hM.unr PP fun k hk => ?_
  rcases GlobalTheory.StepLaw.div_or_isConjPl_div D L.C.P k PP hk with h | ⟨PP', h, hc⟩
  · exact h1 ((hL.Pg PP).2 ⟨k, h⟩)
  · exact h2 ⟨PP', (hL.Pg PP').2 ⟨k, h⟩, hc⟩

end Adelic

open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.FrameEquiv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

theorem chiDet_mul_mu_eq_one : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : Formalism.IndefR.Links.RealDat D A Ks) (i : Fin D.R.m), R.toLevCh.Is A.μ0 → ∀ mu : GA D (Formalism.IndefR.Links.Wc D i) → ℂ, MuVal (Formalism.IndefR.Links.Wc D i) (R.mu0 ((i : ℕ) + 1)) mu → ∀ (g : G) (k : GA D (Formalism.IndefR.Links.Wc D i)), Formalism.IndefR.Lev.IsLevelLift (Formalism.IndefR.Links.Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k → (∏ PP : R.Pg, ((R.chi ((i : ℕ) + 1) PP.1 (Matrix.GeneralLinearGroup.det (R.eG g PP)) : ℂˣ) : ℂ)) * mu k = 1 := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R i hL mu hV g k hk
  obtain ⟨hf, hp, hr⟩ := hk
  obtain ⟨e, he⟩ := exists_idemSum R.Pg (GlobalTheory.TypePlaces.not_isConjPl R.C.P R.Pg hL.Pg)
  have hrk : (Formalism.IndefR.Links.Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  rw [mu_eq_prod hV he (tame_on_base_character hL i he) hf (Formalism.L2.DIV.parLev_St hp), ← Finset.prod_coe_sort R.Pg,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun PP _ => ?_
  have h1 : Matrix.GeneralLinearGroup.det (R.eG g PP) = Matrix.GeneralLinearGroup.det
      (Formalism.L2.DIV.redFn (R.βW i) PP.1 (Formalism.IndefR.Lev.finE (Formalism.IndefR.Links.Wc D i) k)) :=
    (congrArg Matrix.GeneralLinearGroup.det (congrFun hr PP)).symm.trans
      (det_restricted_block (Formalism.IndefR.Links.r_le_rank_Wc i) hrk _)
  rw [h1, MonoidHom.inv_apply, Units.mul_inv]

end GlobalTheory.MuLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorIrreducibleModules
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.TensIrr

open Formalism.BasicNotions.TH GlobalTheory.RealLift

section Lin

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

theorem atPl_add (w : ι) (a b : Module.End ℂ (V w)) : atPl w (a + b) = atPl w a + atPl w b :=
  PiTensorProduct.map_update_add _ w a b

theorem atPl_smul (w : ι) (c : ℂ) (a : Module.End ℂ (V w)) : atPl w (c • a) = c • atPl w a :=
  PiTensorProduct.map_update_smul _ w c a

theorem atPl_mul (w : ι) (a b : Module.End ℂ (V w)) : atPl w (a * b) = atPl w a * atPl w b := by
  unfold atPl
  rw [← PiTensorProduct.map_mul]
  congr 1
  funext j
  by_cases h : j = w
  · subst h; simp
  · simp [Function.update_of_ne h]; rfl

theorem atPl_one (w : ι) : atPl (V := V) w 1 = 1 := by
  unfold atPl
  show PiTensorProduct.map (Function.update (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w LinearMap.id) = 1
  rw [Function.update_eq_self]
  exact PiTensorProduct.map_id

theorem atPl_tprod (w : ι) (L : Module.End ℂ (V w)) (v : ∀ i, V i) :
    atPl w L (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (Function.update v w (L (v w))) := by
  unfold atPl
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext j
  by_cases h : j = w
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem atPl_local (w : ι) (y : ⨂[ℂ] i, V i) : ∃ s : Finset (V w), ∀ f g : Module.End ℂ (V w),
    (∀ m ∈ s, f m = g m) → atPl w f y = atPl w g y := by
  classical
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    refine ⟨{v w}, fun f g h => ?_⟩
    rw [map_smul, map_smul, atPl_tprod, atPl_tprod, h (v w) (Finset.mem_singleton_self _)]
  | add x y hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨t, ht⟩ := hy
    refine ⟨s ∪ t, fun f g h => ?_⟩
    rw [map_add, map_add, hs f g (fun m hm => h m (Finset.mem_union_left _ hm)),
      ht f g (fun m hm => h m (Finset.mem_union_right _ hm))]

theorem stable_all (w : ι) {Z : Type} (A : Z → Module.End ℂ (V w)) [Nontrivial (V w)]
    (hirr : ∀ N : Submodule ℂ (V w), (∀ z, ∀ y ∈ N, A z y ∈ N) → N = ⊥ ∨ N = ⊤)
    (hsch : ∀ T : V w →ₗ[ℂ] V w, (∀ z, T ∘ₗ A z = A z ∘ₗ T) → ∃ c : ℂ, T = c • LinearMap.id)
    (N : Submodule ℂ (⨂[ℂ] i, V i)) (hN : ∀ z, ∀ y ∈ N, atPl w (A z) y ∈ N) :
    ∀ f : Module.End ℂ (V w), ∀ y ∈ N, atPl w f y ∈ N := by
  have hadj : ∀ r ∈ Algebra.adjoin ℂ (Set.range A), ∀ y ∈ N, atPl w r y ∈ N := by
    intro r hr
    induction hr using Algebra.adjoin_induction with
    | mem x hx => obtain ⟨z, rfl⟩ := hx; exact hN z
    | algebraMap c =>
      intro y hy
      rw [Algebra.algebraMap_eq_smul_one, atPl_smul, atPl_one]
      exact N.smul_mem c hy
    | add x y _ _ hx hy =>
      intro z hz
      rw [atPl_add]
      exact N.add_mem (hx z hz) (hy z hz)
    | mul x y _ _ hx hy =>
      intro z hz
      rw [atPl_mul]
      exact hx _ (hy z hz)
  intro f y hy
  obtain ⟨s, hs⟩ := atPl_local w y
  obtain ⟨r, hr, hf⟩ := GlobalTheory.IrrTensor.density A hirr hsch f s
  rw [hs f r hf]
  exact hadj r hr y hy

theorem stable_map (N : Submodule ℂ (⨂[ℂ] i, V i))
    (hN : ∀ w (f : Module.End ℂ (V w)), ∀ y ∈ N, atPl w f y ∈ N) (g : ∀ i, Module.End ℂ (V i)) :
    ∀ y ∈ N, PiTensorProduct.map g y ∈ N := by
  classical
  have key : ∀ s : Finset ι, ∀ y ∈ N,
      PiTensorProduct.map (fun i => if i ∈ s then g i else LinearMap.id) y ∈ N := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro y hy; simpa using hy
    | insert a s ha ih =>
      intro y hy
      have e : PiTensorProduct.map (fun i => if i ∈ insert a s then g i else LinearMap.id) =
          atPl a (g a) ∘ₗ PiTensorProduct.map (fun i => if i ∈ s then g i else LinearMap.id) := by
        unfold atPl
        rw [← PiTensorProduct.map_comp]
        congr 1
        funext j
        by_cases h : j = a
        · subst h; simp [ha]
        · simp [Function.update_of_ne h, Finset.mem_insert, h]
      rw [e]
      exact hN a _ _ (ih y hy)
  intro y hy
  simpa using key Finset.univ y hy

def prodForm (ℓ : ∀ i, Module.Dual ℂ (V i)) : (⨂[ℂ] i, V i) →ₗ[ℂ] ℂ :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap ℓ)

theorem prodForm_tprod (ℓ : ∀ i, Module.Dual ℂ (V i)) (v : ∀ i, V i) :
    prodForm ℓ (PiTensorProduct.tprod ℂ v) = ∏ i, ℓ i (v i) := by
  simp [prodForm]

theorem map_rankOne (ℓ : ∀ i, Module.Dual ℂ (V i)) (u : ∀ i, V i) (y : ⨂[ℂ] i, V i) :
    PiTensorProduct.map (fun i => (ℓ i).smulRight (u i)) y = prodForm ℓ y • PiTensorProduct.tprod ℂ u := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    rw [map_smul, map_smul, PiTensorProduct.map_tprod, prodForm_tprod, smul_assoc]
    congr 1
    simp only [LinearMap.smulRight_apply]
    exact MultilinearMap.map_smul_univ _ _ _
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_smul]

end Lin

end GlobalTheory.TensIrr

namespace GlobalTheory.TensIrr

open Formalism.BasicNotions.TH GlobalTheory.RealLift
open scoped Matrix

section Lin2

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

theorem exists_prodForm_ne (y : ⨂[ℂ] i, V i) (hy : y ≠ 0) : ∃ ℓ : ∀ i, Module.Dual ℂ (V i), prodForm ℓ y ≠ 0 := by
  classical
  let b := fun i => Module.Basis.ofVectorSpace ℂ (V i)
  let B := Basis.piTensorProduct b
  obtain ⟨α, hα⟩ : ∃ α, B.repr y α ≠ 0 := by
    by_contra h
    push_neg at h
    apply hy
    apply B.repr.injective
    ext α
    simp [h α]
  refine ⟨fun i => (b i).coord (α i), ?_⟩
  have e : (Finsupp.lapply α ∘ₗ B.repr.toLinearMap) = prodForm (fun i => (b i).coord (α i)) := by
    refine B.ext fun β => ?_
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.lapply_apply,
      show B β = _ from Basis.piTensorProduct_apply b β, prodForm_tprod]
    simp only [Module.Basis.coord_apply, Module.Basis.repr_self]
    by_cases h : β = α
    · subst h; simp
    · obtain ⟨i, hi⟩ := Function.ne_iff.1 h
      rw [Finsupp.single_apply, if_neg h]
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [Finsupp.single_apply, if_neg hi])
  rw [← e]
  simpa using hα

theorem tensor_nontrivial [∀ i, Nontrivial (V i)] : Nontrivial (⨂[ℂ] i, V i) := by
  choose v hv using fun i => exists_ne (0 : V i)
  choose ℓ hℓ using fun i => Module.Projective.exists_dual_eq_one ℂ (hv i)
  refine nontrivial_of_ne (PiTensorProduct.tprod ℂ v) 0 fun h => ?_
  have := congrArg (prodForm ℓ) h
  rw [prodForm_tprod, map_zero] at this
  simp [hℓ] at this

theorem irr_of_stable (N : Submodule ℂ (⨂[ℂ] i, V i))
    (hN : ∀ w (f : Module.End ℂ (V w)), ∀ y ∈ N, atPl w f y ∈ N) : N = ⊥ ∨ N = ⊤ := by
  by_cases h : N = ⊥
  · exact Or.inl h
  right
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  obtain ⟨ℓ, hℓ⟩ := exists_prodForm_ne y hy0
  rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
  rintro _ ⟨u, rfl⟩
  have h1 := stable_map N hN (fun i => (ℓ i).smulRight (u i)) y hy
  rw [map_rankOne] at h1
  have h2 := N.smul_mem (prodForm ℓ y)⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ hℓ, one_smul] at h2

end Lin2

theorem Jm_conjTranspose (R S : ℕ) : (Jm R S)ᴴ = Jm R S := by
  simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose]

theorem Jm_mul_self (R S : ℕ) : Jm R S * Jm R S = 1 := by
  simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

theorem mem_upq_comb {R S : ℕ} (Z : Mat R S) (a b : ℂ) (h : star a + b = 0) :
    a • Z + b • (Jm R S * Zᴴ * Jm R S) ∈ upq R S := by
  have hJh := Jm_conjTranspose R S
  have hJJ := Jm_mul_self R S
  set J := Jm R S
  have e1 : J * (Z * J) * J = J * Z := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hJJ, Matrix.mul_one]
  have e2 : J * (J * Zᴴ * J) = Zᴴ * J := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have hb : b = -star a := by linear_combination h
  show (a • Z + b • (J * Zᴴ * J))ᴴ * J + J * (a • Z + b • (J * Zᴴ * J)) = 0
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, hJh, Matrix.conjTranspose_conjTranspose, Matrix.add_mul, Matrix.mul_add,
    Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, e1, e2, hb]
  simp only [star_neg, star_star, neg_smul]
  abel

theorem upq_decomp {R S : ℕ} (Z : Mat R S) : ∃ X₁ ∈ upq R S, ∃ X₂ ∈ upq R S, Z = X₁ + Complex.I • X₂ := by
  refine ⟨(1 / 2 : ℂ) • Z + (-(1 / 2) : ℂ) • (Jm R S * Zᴴ * Jm R S), mem_upq_comb Z _ _ (by simp),
    (-(Complex.I / 2)) • Z + (-(Complex.I / 2)) • (Jm R S * Zᴴ * Jm R S), mem_upq_comb Z _ _ ?_, ?_⟩
  · simp [Complex.conj_I]; ring
  · rw [smul_add, smul_smul, smul_smul]
    have : Complex.I * -(Complex.I / 2) = 1 / 2 := by ring_nf; simp; ring
    rw [this]
    module

theorem tensor_irr : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (R S : ℕ) (M : ι → Formalism.BasicNotions.TH.GKMod R S),
    (∀ i, Formalism.MainNotions.SchurIrreducible.IrrGK (M i) ∧ GlobalTheory.RealLift.ScalarEnd (M i)) →
    Nontrivial (PiTensorProduct ℂ fun i => (M i).V) ∧
    ∀ N : Submodule ℂ (PiTensorProduct ℂ fun i => (M i).V),
      (∀ i, ∀ Z ∈ Formalism.BasicNotions.TH.upq R S, ∀ y ∈ N, GlobalTheory.RealLift.atPl i ((M i).act Z) y ∈ N) → N = ⊥ ∨ N = ⊤ := by
  intro ι _ _ R S M hM
  haveI : ∀ i, Nontrivial (M i).V := fun i => (hM i).1.1
  refine ⟨tensor_nontrivial, fun N hN => irr_of_stable N ?_⟩
  have hgl : ∀ i (Z : Mat R S), ∀ y ∈ N, atPl i ((M i).act Z) y ∈ N := by
    intro i Z y hy
    obtain ⟨X₁, h₁, X₂, h₂, rfl⟩ := upq_decomp Z
    rw [map_add, map_smul, atPl_add, atPl_smul, LinearMap.add_apply, LinearMap.smul_apply]
    exact N.add_mem (hN i X₁ h₁ y hy) (N.smul_mem _ (hN i X₂ h₂ y hy))
  intro w f y hy
  exact stable_all (V := fun i => (M i).V) w (fun Z => (M w).act Z) (hM w).1.2 (hM w).2 N (hgl w) f y hy

end GlobalTheory.TensIrr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralParabolicUnfoldLevi
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LeviDesc

theorem cavg_conj_KGL : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (w : Pl E) (f : GLw n w → ℂ), (∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' f) → ∀ k ∈ GlobalTheory.LFun.KGL w n, ∀ x, GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w n) f (k⁻¹ * x * k) = GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w n) f x := by
  intro E _ _ n w f _ k hk x
  unfold GlobalTheory.LeviDesc.cavg
  rw [← GlobalTheory.TwOrbConj.avg_left (fun k' : GlobalTheory.LFun.KGL w n => f ((k' : GLw n w)⁻¹ * x * k')) ⟨k, hk⟩]
  congr 1
  funext k'
  congr 1
  simp only [Subgroup.coe_mul, _root_.mul_inv_rev]
  group

theorem twistedOrbitalIntegral_parabolic_unfolding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∀ (n a : ℕ) (ha : a ≤ n) (w : Pl E) (f : GLw n w → ℂ), (∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' f) → ∀ m : GLw a w × GLw (n - a) w, (m.1.val.charpoly * m.2.val.charpoly).Separable → ∀ hγ : blk (Nat.add_sub_cancel' ha) w m 0 ∈ GlobalTheory.LeviDesc.parP a n w, twOrb (MonoidHom.id (GlobalTheory.LeviDesc.parP a n w)) ((GlobalTheory.LFun.KGL w n).subgroupOf (GlobalTheory.LeviDesc.parP a n w)) ⟨_, hγ⟩ (fun p => GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w n) f (p : GLw n w)) = twOrb (MonoidHom.id _) ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w (n - a))) m (GlobalTheory.LeviDesc.orbN (Nat.add_sub_cancel' ha) w f) := by
  intro E _ _ _ n a ha w f hf m hsep hγ
  obtain ⟨s, π, u, hs, hu, hπs, hinj, hker, hKs, hKπ, hKu⟩ := GlobalTheory.T.exists_blockUpperParabolic_levi_projection_unipotent E n a (n - a) (Nat.add_sub_cancel' ha) w
  have hγs : (⟨blk (Nat.add_sub_cancel' ha) w m 0, hγ⟩ : GlobalTheory.LeviDesc.parP a n w) = s m := Subtype.ext (hs m).symm
  have hfin := GlobalTheory.T.finite_parabolicDoubleCosets_orbitalIntegral E n a (n - a) (Nat.add_sub_cancel' ha) w f hf m hsep hγ
  have hcent := GlobalTheory.T.mem_twisted_centralizer_block_iff E n a (n - a) (Nat.add_sub_cancel' ha) w m hsep hγ
  have hcpt := GlobalTheory.T.mem_compactPart_parabolicCentralizer_iff_blockDiagonal E n a (n - a) (Nat.add_sub_cancel' ha) w m hsep hγ
  rw [hγs] at hfin hcent hcpt ⊢
  have hrhs : GlobalTheory.LeviDesc.orbN (Nat.add_sub_cancel' ha) w f = fun m' => hint (intMat a (n - a) w) (fun X =>
      (fun p : GlobalTheory.LeviDesc.parP a n w => GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w n) f (p : GLw n w)) ((u X)⁻¹ * s m' * u X)) := by
    funext m'
    unfold GlobalTheory.LeviDesc.orbN
    refine congrArg (hint (intMat a (n - a) w)) (funext fun X => ?_)
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, hs, hu]
  rw [hrhs]
  refine GlobalTheory.T.orbitalIntegral_semidirectProduct_unfolding _ _ _ s π u hπs hinj hker _ _ (intMat a (n - a) w) hKs hKπ hKu m ?_ ?_ ?_ ?_ _ ?_ hfin
  · intro p
    rw [hcent]
    simp only [Subtype.ext_iff, hs]
  · intro p
    rw [hcpt]
    simp only [Subtype.ext_iff, hs]
  · intro q
    exact GlobalTheory.T.centralizer_inf_conj_integralGLProd_le_cptPart E a (n - a) w m q
  · intro X
    obtain ⟨U, hU, hUi, hUk⟩ := GlobalTheory.T.exists_finiteIndex_levi_subgroup_unipotentConj_integral E n a (n - a) (Nat.add_sub_cancel' ha) w (Multiplicative.toAdd X)
    refine ⟨U, hU, hUi, fun k hk => ?_⟩
    rw [Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, hs, hu]
    exact hUk k hk
  · intro k hk x
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
    exact cavg_conj_KGL E n w f hf _ (Subgroup.mem_subgroupOf.1 hk) _

end GlobalTheory.LeviDesc
end
end

