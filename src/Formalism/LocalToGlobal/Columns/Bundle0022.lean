import Formalism.LocalToGlobal.Columns.Bundle0020
import Formalism.LocalToGlobal.HermitianForms.Bundle0005
import Formalism.LocalToGlobal.Columns.WordFin
import Formalism.LocalToGlobal.Columns.Bundle0017
import Formalism.LocalToGlobal.Columns.Bundle0021
import Formalism.LocalToGlobal.Columns.RecLevelHost

-- bundled from Formalism.LocalToGlobal.Columns.LastVectorMemSpan
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Mat

variable {E V : Type} [Field E] [AddCommGroup V] [Module E V]

theorem hq_toGLb_mulVec {n : ℕ} (b : Basis (Fin n) E V) (γ : V ≃ₗ[E] V) (x : V) :
    ((Formalism.L2.Herm.toGLb b γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ b.equivFun x = b.equivFun (γ x) :=
  LinearMap.toMatrix_mulVec_repr b b (γ : V →ₗ[E] V) x

def hqCrd {n N : ℕ} (b : Basis (Fin n) E V) (h : n = N) : V ≃ₗ[E] (Fin N → E) :=
  b.equivFun.trans (LinearEquiv.funCongrLeft E E (finCongr h).symm)

theorem hq_reGL_mulVec {n N : ℕ} (b : Basis (Fin n) E V) (h : n = N) (γ : V ≃ₗ[E] V) (x : V) :
    ((Formalism.L2.Forms.reGL h E (Formalism.L2.Herm.toGLb b γ) : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ hqCrd b h x = hqCrd b h (γ x) := by
  subst h
  rw [Formalism.L2.Forms.reGL_rfl]
  exact hq_toGLb_mulVec b γ x

def hqLin {n N : ℕ} (b : Basis (Fin n) E V) (h : n = N) (g : GL (Fin N) E) : V ≃ₗ[E] V :=
  (Formalism.L2.Herm.toGLb b).symm ((Formalism.L2.Forms.reGL h E).symm g)

theorem hqLin_re {n N : ℕ} (b : Basis (Fin n) E V) (h : n = N) (g : GL (Fin N) E) :
    Formalism.L2.Forms.reGL h E (Formalism.L2.Herm.toGLb b (hqLin b h g)) = g := by
  unfold hqLin
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

theorem hqLin_crd {n N : ℕ} (b : Basis (Fin n) E V) (h : n = N) (g : GL (Fin N) E) (x : V) :
    hqCrd b h (hqLin b h g x) = (g : Matrix (Fin N) (Fin N) E) *ᵥ hqCrd b h x := by
  have := hq_reGL_mulVec b h (hqLin b h g) x
  rw [hqLin_re] at this
  exact this.symm

end Mat

section Form

variable {A n : Type} [CommRing A] [Fintype n] [DecidableEq n]

theorem hq_hform_dot (σ : A →+* A) (J : Matrix n n A) (x y : n → A) : hform σ J x y = (σ ∘ x) ⬝ᵥ (J *ᵥ y) := by
  simp only [hform, dotProduct, mulVec, Function.comp, Finset.mul_sum, mul_assoc]

theorem hq_hform_UJ (σ : A →+* A) (J : Matrix n n A) (g : GL n A) (hg : g ∈ UJ σ J) (x y : n → A) :
    hform σ J ((g : Matrix n n A) *ᵥ x) ((g : Matrix n n A) *ᵥ y) = hform σ J x y := by
  have hτ : σ ∘ ((g : Matrix n n A) *ᵥ x) = (g : Matrix n n A).map σ *ᵥ (σ ∘ x) := by
    funext i
    exact RingHom.map_mulVec σ (g : Matrix n n A) x i
  have hg' : cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J := hg
  rw [hq_hform_dot, hq_hform_dot, hτ, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
  show _ ⬝ᵥ ((cT σ (g : Matrix n n A) * J * (g : Matrix n n A)) *ᵥ y) = _
  rw [hg']

end Form

variable {D : ColRec}

theorem hq_crdN (i : ℕ) (hi : i ≤ D.R.m) : CF.crdN D i hi = hqCrd (D.sp.X i).frame (CF.rankN D i hi) := rfl

def hqG (i : ℕ) (hi : i ≤ D.R.m) (g : UJ (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D i hi)) : CH.GX D i :=
  ⟨hqLin (D.sp.X i).frame (CF.rankN D i hi) g.1, fun x y => by
    rw [hx_hform i hi, hx_hform i hi, hq_crdN, hqLin_crd, hqLin_crd]
    exact hq_hform_UJ _ _ g.1 g.2 _ _⟩

theorem hqG_crd (i : ℕ) (hi : i ≤ D.R.m) (g : UJ (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D i hi)) (x : (D.sp.X i).V) :
    CF.crdN D i hi ((hqG i hi g).1 x) = (g.1 : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) *ᵥ CF.crdN D i hi x :=
  hqLin_crd _ _ g.1 x

theorem hqG_re (i : ℕ) (hi : i ≤ D.R.m) (g : UJ (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D i hi)) :
    Formalism.L2.Forms.reGL (CF.rankN D i hi) D.host.E (Formalism.L2.Herm.toGLb (D.sp.X i).frame (hqG i hi g).1) = g.1 :=
  hqLin_re _ _ g.1

theorem hqG_gmap (i : ℕ) (hi : i ≤ D.R.m) (g : UJ (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D i hi))
    (L : Submodule (𝓞 D.host.E) (D.sp.X i).V) :
    (gmap (hqG i hi g).1 L).map
        ((CF.crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E)) =
      Formalism.L2.Forms.mulLat (g.1 : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) (L.map
        ((CF.crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E))) := by
  unfold gmap Formalism.L2.Forms.mulLat
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro x
  exact hqG_crd i hi g x

theorem hq_map_inj (i : ℕ) (hi : i ≤ D.R.m) : Function.Injective (Submodule.map
    ((CF.crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E))) :=
  Submodule.map_injective_of_injective (CF.crdN D i hi).injective

variable {u : D.what₂.Word} {A : CF.AtTTied u} {P : ∀ i hi, CF.LvTied u A i hi} {K : CF.ClsPTied u}

def hqLatP (K : CF.ClsPTied u) (c : (D.fm u).clsP) : Submodule (𝓞 D.host.E) D.sp.X'.V :=
  (K.lat c).map (((CF.crdP D).symm : (Fin (D.R.N D.R.m - 1) → D.host.E) →ₗ[D.host.E] D.sp.X'.V).restrictScalars (𝓞 D.host.E))

theorem hqLatP_crd (K : CF.ClsPTied u) (c : (D.fm u).clsP) :
    K.lat c = (hqLatP K c).map
      ((CF.crdP D : D.sp.X'.V →ₗ[D.host.E] (Fin (D.R.N D.R.m - 1) → D.host.E)).restrictScalars (𝓞 D.host.E)) := by
  unfold hqLatP
  rw [← Submodule.map_comp]
  symm
  convert Submodule.map_id _
  ext x j
  simp

variable (T : CF.TilTied u A K (P D.R.m le_rfl))

def lastSpaceVector : (D.sp.X D.R.m).V := (CF.crdN D D.R.m le_rfl).symm T.z0

theorem lastVector_coords : T.z0 = CF.crdN D D.R.m le_rfl (lastSpaceVector T) := ((CF.crdN D D.R.m le_rfl).apply_symm_apply T.z0).symm

theorem lastVector_mem_span : lastSpaceVector T ∈ Submodule.span D.host.E {D.sp.z} := by
  obtain ⟨a, ha⟩ := T.lastCoordinateUniformizerVector_spans_orthogonal_line
  refine Submodule.mem_span_singleton.2 ⟨a, ?_⟩
  unfold lastSpaceVector
  rw [LinearEquiv.eq_symm_apply, map_smul, ha]
  rfl

theorem lastVector_norm : (D.sp.X D.R.m).hT (lastSpaceVector T) (lastSpaceVector T) = ((D.mem u).A.T : D.host.E) := by
  rw [hx_hform D.R.m le_rfl, ← lastVector_coords]
  exact T.hermitianForm_lastCoordinateUniformizerVector_self

def hqTilG (c : (D.fm u).clsP) : CH.GX D D.R.m := hqG D.R.m le_rfl (T.ga c)

set_option maxHeartbeats 1000000 in
theorem hq_til_lat (c : (D.fm u).clsP) :
    gmap (hqTilG T c).1 (D.clsLat u D.R.m ((D.fm u).til c)) =
      (hqLatP K c).map (D.sp.iX'.restrictScalars (𝓞 D.host.E)) ⊔ Submodule.span (𝓞 D.host.E) {lastSpaceVector T} := by
  apply hq_map_inj D.R.m le_rfl
  rw [hqTilG, hqG_gmap, ← hx_clsCrd, T.til_lat c, Submodule.map_sup, Submodule.map_span, Set.image_singleton]
  congr 1
  · unfold hqLatP
    rw [← Submodule.map_comp, ← Submodule.map_comp]
    rfl
  · congr 2
    exact lastVector_coords T

set_option maxHeartbeats 1000000 in
theorem hq_til_fv (c : (D.fm u).clsP) (v : (D.mem u).A.vT) (z : CH.Ld D u D.R.m ((D.fm u).til c)) (a : 𝓞 D.host.E)
    (ha : (a : D.host.E) = (D.sp.X D.R.m).hT (lastSpaceVector T) ((hqTilG T c).1 (z : (D.sp.X D.R.m).V))) :
    (D.fm u).fv D.R.m v _ (hxPr A P D.R.m v _ z) = A.res v a := by
  rw [hxPr_eq A P D.R.m le_rfl]
  refine T.til_fv v c (hxLd D.R.m le_rfl _ z) a ?_
  rw [ha, hx_hform D.R.m le_rfl, ← lastVector_coords, hqTilG, hqG_crd]
  rfl

set_option maxHeartbeats 4000000 in

def xpOf (levP : Formalism.L2.Herm.StepLevel0 D.sp.cm D.sp.X' D.host.g (Formalism.L2.Herm.crdLat D.sp.X' D.sp.X'.L0))
    (clsP : Formalism.L2.Herm.ClassTie D.sp.cm D.sp.X' (Formalism.L2.Herm.crdLat D.sp.X' D.sp.X'.L0) levP.U (D.fm u).stabilizer₂ (hqLatP K)) :
    AtTXp A P where
  lattice₂ := hqLatP K
  levP := levP
  clsP := clsP
  z0 := lastSpaceVector T
  cocycle_zero_mem_invariants := lastVector_mem_span T
  hermitianForm_lastCoordinateUniformizerVector_self := lastVector_norm T
  tilG := hqTilG T
  til_tie := fun c => ⟨hq_til_lat T c, fun v z a ha => hq_til_fv T c v z a ha⟩

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TiedCrd
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure SpStd (B : ColBase) : Prop where
  X_on : ∀ i, i ≤ B.R.m → ∀ a b, (B.sp.X i).hT ((B.sp.X i).frame a) ((B.sp.X i).frame b) = if a = b then 1 else 0
  selfDual_span_frame_X : ∀ i, i ≤ B.R.m → (B.sp.X i).L0 = Submodule.span (𝓞 B.host.E) (Set.range (B.sp.X i).frame)
  P_on : ∀ a b, B.sp.X'.hT (B.sp.X'.frame a) (B.sp.X'.frame b) = if a = b then 1 else 0
  selfDual_span_frame_auxiliary : B.sp.X'.L0 = Submodule.span (𝓞 B.host.E) (Set.range B.sp.X'.frame)
  iX' : ∀ (a : Fin B.sp.X'.rank) (b : Fin (B.sp.X B.R.m).rank), (a : ℕ) = b →
    B.sp.iX' (B.sp.X'.frame a) = (B.sp.X B.R.m).frame b
  z : ∃ c : B.host.E, ∀ b : Fin (B.sp.X B.R.m).rank, (b : ℕ) + 1 = (B.sp.X B.R.m).rank → B.sp.z = c • (B.sp.X B.R.m).frame b

structure HostHyp (d : ColDat) : Prop where
  embE_φ₀ : d.what₂.embLL.comp d.embE = d.host.φ₀
  piT_K : ∀ u, (d.piT u : d.host.E) ∈ d.host.K
  piG_K : ∀ i, (d.piG i : d.host.E) ∈ d.host.K
  cond_eq : d.cond = d.host.QS * d.host.q * d.host.d
  val_eq : ∀ w (x : d.what₂.LL), x ≠ 0 → d.what₂.places.val w x = ((vAdd (d.plEq w) x : ℤ) : WithTop ℤ)

variable {d : ColDat} (a : ColArgs d)

theorem gramN_eq (hS : SpStd d.toColBase) (i : ℕ) (hi : i ≤ d.R.m) : CF.gramN (d.colRec a) i hi = 1 := by
  refine Matrix.ext fun x y => ?_
  show (d.sp.X i).hT ((d.sp.X i).frame _) ((d.sp.X i).frame _) = _
  rw [hS.X_on i hi, Matrix.one_apply]
  simp only [EmbeddingLike.apply_eq_iff_eq]

theorem gramP_eq (hS : SpStd d.toColBase) : CF.gramP (d.colRec a) = 1 := by
  refine Matrix.ext fun x y => ?_
  show d.sp.X'.hT (d.sp.X'.frame _) (d.sp.X'.frame _) = _
  rw [hS.P_on, Matrix.one_apply]
  simp only [EmbeddingLike.apply_eq_iff_eq]

theorem clsCrd_eq (u : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m) (c : StCl (Pr := d.Pr) d.W d.lev u i) :
    CF.clsCrd (d.colRec a) u i hi c = (d.repr u i c).1.L := by
  show (d.clsLat u i c).map (((d.crd i hi : (d.sp.X i).V ≃ₗ[d.host.E] (Fin (d.R.N i) → d.host.E)) :
    (d.sp.X i).V →ₗ[d.host.E] (Fin (d.R.N i) → d.host.E)).restrictScalars (𝓞 d.host.E)) = _
  unfold ColDat.clsLat
  rw [dif_pos hi, ← Submodule.map_comp]
  convert Submodule.map_id _
  ext x j
  simp

theorem embT_eq (hH : HostHyp d) : CF.embT (d.colRec a) = d.X.embC d.σ₀ := by
  funext τ
  show d.host.φ₀.comp _ = (d.what₂.embLL).comp (d.embE.comp _)
  rw [← hH.embE_φ₀, RingHom.comp_assoc]

theorem T_eq (u : d.what₂.Word) : ((d.colRec a).mem u).A.T = d.T u := rfl

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TiedGlPl
section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.UG Formalism.UG.P Formalism.L2.DIV
open Formalism.L2.Forms (kv redM)

section Ker

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : Formalism.BasicNotions.CMData F E)
  (v : HeightOneSpectrum (𝓞 F)) (spl : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
  (halg : ∀ a : v.adicCompletion F, spl ((1 : E) ⊗ₜ[F] a) = (a, a))

theorem glk_val_lt (x : v.adicCompletionIntegers F) (h : IsLocalRing.residue (v.adicCompletionIntegers F) x = 0) :
    Valued.v (x : v.adicCompletion F) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h
  have hle := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 x.2
  refine lt_of_le_of_ne hle fun h1 => h ?_
  have hx0 : (x : v.adicCompletion F) ≠ 0 := fun h0 => by rw [h0, map_zero] at h1; exact zero_ne_one h1
  let y : v.adicCompletionIntegers F := ⟨(x : v.adicCompletion F)⁻¹,
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).2 (by rw [map_inv₀, h1, inv_one])⟩
  have hxy : x * y = 1 := Subtype.ext (mul_inv_cancel₀ hx0)
  exact ⟨⟨x, y, hxy, (mul_comm _ _).trans hxy⟩, rfl⟩

theorem gloRho_oToS (a : 𝓞 E) : gloRho v spl halg (oToS F E a) = IsLocalRing.residue (v.adicCompletionIntegers F)
    ⟨gloPhi v spl (inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E a)), by
      have := gloPhi_int v spl halg _ (afsplit_prV_int v _ (oToS F E a).2)
      rwa [show ((oToS F E a : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) =
        inclE (F := F) (Formalism.L2.Herm.Af F) (algebraMap (𝓞 E) E a) from rfl, afsplit_prV_inclE] at this⟩ := by
  rw [gloRho_apply]
  congr 1

include hc in

theorem glk_ker (w : Pl E) (hov : IsOver v w) (ϖ : 𝓞 E) (h2 : cO E ϖ ∉ w.asIdeal)
    (hval : Valued.v (gloPhi v spl (inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E ϖ))) < 1) :
    ∀ a ∈ w.asIdeal, gloRho v spl halg (oToS F E a) = 0 := by
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    exact h2 (by rw [map_zero]; exact zero_mem _)
  have hϖ : gloRho v spl halg (oToS F E ϖ) = 0 := by
    rw [gloRho_oToS]
    exact glo_res_zero v _ hval
  let Q : Pl E :=
    { asIdeal := RingHom.ker ((gloRho v spl halg).comp (oToS F E))
      isPrime := RingHom.ker_isPrime _
      ne_bot := fun hb => hϖ0 (by
        have : ϖ ∈ RingHom.ker ((gloRho v spl halg).comp (oToS F E)) := hϖ
        rwa [hb, Ideal.mem_bot] at this) }
  have hQ : IsOver v Q := by
    show v.asIdeal = Q.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))
    ext r
    rw [Ideal.mem_comap]
    show r ∈ v.asIdeal ↔ gloRho v spl halg (oToS F E (algebraMap (𝓞 F) (𝓞 E) r)) = 0
    rw [gloRho_algMap]
    constructor
    · intro hr
      refine glo_res_zero v _ ?_
      show Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) r) < 1
      rw [csApprox_val_int]
      exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v r).2 hr
    · intro hr
      have := glk_val_lt v _ hr
      change Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) r) < 1 at this
      rw [csApprox_val_int] at this
      exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v r).1 this
  rcases rll_over_cases hc hov hQ with h | h
  · intro a ha
    have : a ∈ Q.asIdeal := by rw [h]; exact ha
    exact this
  · exfalso
    have : ϖ ∈ Q.asIdeal := hϖ
    rw [h, mem_conjP] at this
    exact h2 this

end Ker

section Pl

variable {X : Fields} {Pr : Primes X} (hc : Formalism.BasicNotions.CMData X.F X.E) (hPr : Pr.Ok)

structure GSplit where
  sp : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)), (Pr.g i : 𝓞 X.F) ∈ v.asIdeal →
    X.E ⊗[X.F] v.adicCompletion X.F ≃+* v.adicCompletion X.F × v.adicCompletion X.F
  sp_sig : ∀ i v h x, sp i v h (sigR hc.sig (v.adicCompletion X.F) x) = swapR _ (sp i v h x)
  sp_alg : ∀ i v h (a : v.adicCompletion X.F), sp i v h ((1 : X.E) ⊗ₜ[X.F] a) = (a, a)
  sp_pi : ∀ i v h, Valued.v (sp i v h (inclE (F := X.F) (v.adicCompletion X.F) (hc.sig (Pr.piG i : X.E)))).1 < 1

include hc hPr in
theorem glk_under (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)) : v ∈ plUnder X.F (Pr.vG i) ↔ (Pr.g i : 𝓞 X.F) ∈ v.asIdeal := by
  have hne : X.conjO (Pr.piG i) ≠ 0 := by
    intro h0
    have := hPr.piG_norm i
    rw [h0, mul_zero] at this
    exact (Nat.cast_ne_zero.2 (hPr.g_prime i).ne_zero) this.symm
  refine mem_plUnder_iff_norm hc (fun P => mem_divs hne P) (Pr.g i) ?_ v
  have h2 : cO X.E (X.conjO (Pr.piG i)) = Pr.piG i := RingOfIntegers.ext (star_star _)
  rw [h2, mul_comm]; exact hPr.piG_norm i

theorem glk_vG_le (i : Fin 2) {w : Pl X.E} (h : w ∈ Pr.vG i) : w ∈ Pr.vGs := by
  classical
  unfold Primes.vGs
  fin_cases i
  · exact Finset.mem_union_left _ h
  · exact Finset.mem_union_right _ h

def gwOf (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal) : Pr.vGs :=
  ⟨((glk_under hc hPr i v).2 h).choose, glk_vG_le i ((glk_under hc hPr i v).2 h).choose_spec.1⟩

theorem gwOf_mem (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal) :
    (gwOf hc hPr i v h).1 ∈ Pr.vG i := ((glk_under hc hPr i v).2 h).choose_spec.1

theorem gwOf_over (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal) :
    IsOver v (gwOf hc hPr i v h).1 := ((glk_under hc hPr i v).2 h).choose_spec.2

theorem gwOf_uniq (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal) (w' : Pr.vGs)
    (hw' : IsOver v w'.1) : w' = gwOf hc hPr i v h := by
  rcases rll_over_cases hc (gwOf_over hc hPr i v h) hw' with e | e
  · exact Subtype.ext e
  · exact absurd e (rlh_vGs_not_conj hPr (gwOf hc hPr i v h).2 w'.2)

variable {hc}

theorem GSplit.ker (S : GSplit (Pr := Pr) hc) (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal) :
    ∀ a ∈ (gwOf hc hPr i v h).1.asIdeal, gloRho v (S.sp i v h) (S.sp_alg i v h) (oToS X.F X.E a) = 0 := by
  refine glk_ker hc v (S.sp i v h) (S.sp_alg i v h) _ (gwOf_over hc hPr i v h) (X.conjO (Pr.piG i)) ?_ (S.sp_pi i v h)
  have h2 : cO X.E (X.conjO (Pr.piG i)) = Pr.piG i := RingOfIntegers.ext (star_star _)
  rw [h2]
  intro hmem
  have h3 : X.conjO (Pr.piG i) ∈ (gwOf hc hPr i v h).1.asIdeal := decoFin_mem_of_mem_divs (gwOf_mem hc hPr i v h)
  obtain ⟨a, b, e⟩ := hPr.piG_cop i
  apply one_notMem (gwOf hc hPr i v h).1
  rw [← e]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmem) (Ideal.mul_mem_left _ _ h3)

def GSplit.eK (S : GSplit (Pr := Pr) hc) (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal) :
    kP (gwOf hc hPr i v h).1 ≃+* kv X.F v :=
  gloE v (S.sp i v h) (S.sp_alg i v h) _ (S.ker hPr i v h)

include hPr in

theorem GSplit.res_one (S : GSplit (Pr := Pr) hc) (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal)
    (ϖ : 𝓞 X.E) (hϖ : (Pr.g i : 𝓞 X.E) ∣ ϖ - 1) : gloRho v (S.sp i v h) (S.sp_alg i v h) (oToS X.F X.E ϖ) = 1 := by
  obtain ⟨s, hs⟩ := hϖ
  have hg : (Pr.g i : 𝓞 X.E) ∈ (gwOf hc hPr i v h).1.asIdeal := by
    have h1 : (Pr.g i : 𝓞 X.F) ∈ (gwOf hc hPr i v h).1.asIdeal.comap (algebraMap (𝓞 X.F) (𝓞 X.E)) := (gwOf_over hc hPr i v h) ▸ h
    rwa [Ideal.mem_comap, map_natCast] at h1
  have h2 : ϖ = 1 + (Pr.g i : 𝓞 X.E) * s := by rw [← hs]; ring
  rw [h2, map_add, map_add, map_one, map_one, S.ker hPr i v h _ (Ideal.mul_mem_right _ _ hg), add_zero]

def GSplit.unitOf (S : GSplit (Pr := Pr) hc) (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal)
    (ϖ : 𝓞 X.E) (hϖ : (Pr.g i : 𝓞 X.E) ∣ ϖ - 1) : (v.adicCompletionIntegers X.F)ˣ :=
  IsUnit.unit (a := (⟨gloPhi v (S.sp i v h) (inclE (F := X.F) (v.adicCompletion X.F) (algebraMap (𝓞 X.E) X.E ϖ)), by
      have := gloPhi_int v (S.sp i v h) (S.sp_alg i v h) _ (afsplit_prV_int v _ (oToS X.F X.E ϖ).2)
      rwa [show ((oToS X.F X.E ϖ : Formalism.L2.Herm.intAf X.F X.E) : X.E ⊗[X.F] Formalism.L2.Herm.Af X.F) =
        inclE (F := X.F) (Formalism.L2.Herm.Af X.F) (algebraMap (𝓞 X.E) X.E ϖ) from rfl, afsplit_prV_inclE] at this⟩ :
      v.adicCompletionIntegers X.F)) (by
    rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff, ← gloRho_oToS v (S.sp i v h) (S.sp_alg i v h) ϖ,
      S.res_one hPr i v h ϖ hϖ]
    exact one_ne_zero)

theorem GSplit.unitOf_val (S : GSplit (Pr := Pr) hc) (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal)
    (ϖ : 𝓞 X.E) (hϖ : (Pr.g i : 𝓞 X.E) ∣ ϖ - 1) :
    ((S.unitOf hPr i v h ϖ hϖ : v.adicCompletionIntegers X.F) : v.adicCompletion X.F) =
      gloPhi v (S.sp i v h) (inclE (F := X.F) (v.adicCompletion X.F) (algebraMap (𝓞 X.E) X.E ϖ)) := rfl

theorem GSplit.unitOf_res (S : GSplit (Pr := Pr) hc) (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal)
    (ϖ : 𝓞 X.E) (hϖ : (Pr.g i : 𝓞 X.E) ∣ ϖ - 1) :
    IsLocalRing.residue (v.adicCompletionIntegers X.F) (S.unitOf hPr i v h ϖ hϖ) = 1 := by
  rw [← S.res_one hPr i v h ϖ hϖ, gloRho_oToS]
  rfl

include hPr in
theorem glk_piT_cong (u : Pr.Word) (i : Fin 2) : (Pr.g i : 𝓞 X.E) ∣ Pr.piT u - 1 := by
  refine Dvd.dvd.trans ?_ (hPr.piT_cong u)
  have : Pr.g i ∣ Pr.cond * (Pr.g 0 * Pr.g 1) ^ 2 := by
    refine Dvd.dvd.mul_left (Dvd.dvd.trans ?_ (dvd_pow_self _ two_ne_zero)) _
    fin_cases i
    · exact Dvd.intro _ rfl
    · exact Dvd.intro_left _ rfl
  exact Nat.cast_dvd_cast this

end Pl

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TiedMvA
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def SameOffC {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : Ideal (𝓞 E))
    (A B : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  ∀ (q : Ideal (𝓞 E)) (hq : q.IsMaximal), q ≠ P → q ≠ Formalism.HermitianLatticesTheory.conjIdeal (K := E) P →
    haveI := hq.isPrime
    Formalism.HermitianLatticesTheory.localization₂ q A = Formalism.HermitianLatticesTheory.localization₂ q B

variable {D : ColRec} {u : D.what₂.Word} (A : CF.AtTTied u) (P : ∀ i hi, CF.LvTied u A i hi)

set_option maxHeartbeats 4000000 in

structure AtTMovesC where

  upG : ∀ i hi v (c : (D.mem u).C.cls i), ↥(CF.Ld D u i hi c) → UJ (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D i hi)

  up_tie : ∀ i hi v c (y : ↥(CF.Ld D u i hi c)), (D.fm u).fv i v c ((P i hi).pr v c y) = 1 →
    SameOffC (A.Pv v) (Formalism.L2.Forms.mulLat (upG i hi v c y).1.1 (CF.clsCrd D u i hi ((D.fm u).up i v c ((P i hi).pr v c y))))
        (CF.clsCrd D u i hi c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Formalism.L2.Forms.mulLat (upG i hi v c y).1.1 (CF.clsCrd D u i hi ((D.fm u).up i v c ((P i hi).pr v c y)))) =
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (CF.Ld D u i hi c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Formalism.L2.Forms.mulLat (upG i hi v c y).1.1 (CF.Ld D u i hi ((D.fm u).up i v c ((P i hi).pr v c y)))) =
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (CF.Ld D u i hi c ⊔
          Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • y.1}) ∧
      (∀ (z : ↥(CF.Ld D u i hi ((D.fm u).up i v c ((P i hi).pr v c y))))
        (hz : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((upG i hi v c y).1.1 *ᵥ z.1) ∈ CF.Ld D u i hi c),
        (D.fm u).fv i v _ ((P i hi).pr v _ z) = (D.fm u).fv i v c ((P i hi).pr v c ⟨_, hz⟩)) ∧
      (∀ v', v' ≠ v → ∀ (z : ↥(CF.Ld D u i hi ((D.fm u).up i v c ((P i hi).pr v c y))))
        (hz : (upG i hi v c y).1.1 *ᵥ z.1 ∈ CF.Ld D u i hi c),
        (D.fm u).fv i v' _ ((P i hi).pr v' _ z) = (D.fm u).fv i v' c ((P i hi).pr v' c ⟨_, hz⟩))

  dnG : ∀ i hi v (c : (D.mem u).C.cls i), Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c) →
    UJ (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D i hi)

  dn_tie : ∀ i hi v c (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c)), g ≠ 0 →
    SameOffC (A.Pv v) (Formalism.L2.Forms.mulLat (dnG i hi v c g).1.1 (CF.clsCrd D u i hi ((D.fm u).dn i v c g))) (CF.clsCrd D u i hi c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Formalism.L2.Forms.mulLat (dnG i hi v c g).1.1 (CF.Ld D u i hi ((D.fm u).dn i v c g))) =
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (CF.clsCrd D u i hi c) ∧
      (∀ (z : ↥(CF.Ld D u i hi ((D.fm u).dn i v c g))) (hz : (dnG i hi v c g).1.1 *ᵥ z.1 ∈ CF.Lk A i hi v c),
        (D.fm u).fv i v _ ((P i hi).pr v _ z) = g ((P i hi).prk v c ⟨_, hz⟩)) ∧
      (∀ v', v' ≠ v → ∀ (z : ↥(CF.Ld D u i hi ((D.fm u).dn i v c g))) (hz : (dnG i hi v c g).1.1 *ᵥ z.1 ∈ CF.Ld D u i hi c),
        (D.fm u).fv i v' _ ((P i hi).pr v' _ z) = (D.fm u).fv i v' c ((P i hi).pr v' c ⟨_, hz⟩))

  dilG : ∀ i hi v, ((D.mem u).A.Fv v)ˣ → (D.mem u).C.cls i → UJ (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D i hi)

  dil_tie : ∀ i hi v (a : ((D.mem u).A.Fv v)ˣ) c,
      Formalism.L2.Forms.mulLat (dilG i hi v a c).1.1 (CF.clsCrd D u i hi ((D.fm u).dil i v a c)) = CF.clsCrd D u i hi c ∧
      (∀ (z : ↥(CF.Ld D u i hi ((D.fm u).dil i v a c))) (hz : (dilG i hi v a c).1.1 *ᵥ z.1 ∈ CF.Ld D u i hi c),
        (D.fm u).fv i v _ ((P i hi).pr v _ z) = (a : (D.mem u).A.Fv v) * (D.fm u).fv i v c ((P i hi).pr v c ⟨_, hz⟩)) ∧
      (∀ v', v' ≠ v → ∀ (z : ↥(CF.Ld D u i hi ((D.fm u).dil i v a c))) (hz : (dilG i hi v a c).1.1 *ᵥ z.1 ∈ CF.Ld D u i hi c),
        (D.fm u).fv i v' _ ((P i hi).pr v' _ z) = (D.fm u).fv i v' c ((P i hi).pr v' c ⟨_, hz⟩))

end Formalism.L2.Col
end
end

