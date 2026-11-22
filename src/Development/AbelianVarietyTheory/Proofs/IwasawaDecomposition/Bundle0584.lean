import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Formalism.FrobeniusOrbits.HostCorollaries
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0556
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0562
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0572
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0560
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0573
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LetterConjugation
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.TrueGeo

namespace GlobalTheory.Proof.LetterConjugation

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

theorem mem_letters (x : Letter Dw) : x ∈ letters Dw := by
  obtain ⟨τ, i⟩ := x
  obtain ⟨a, rfl⟩ := (Fintype.equivFin (E →+* ℂ)).symm.surjective τ
  exact List.mem_flatMap.2 ⟨a, List.mem_finRange a, List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩⟩

theorem nodup_letters : (letters Dw).Nodup := by
  refine List.nodup_flatMap.2 ⟨fun a _ => ?_, ?_⟩
  · exact (List.nodup_finRange _).map fun i i' h => eq_of_heq (Sigma.mk.inj h).2
  · refine (List.nodup_finRange _).pairwise_of_forall_ne fun a _ b _ hab => ?_
    intro x hx hy
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    obtain ⟨i', -, h⟩ := List.mem_map.1 hy
    exact hab ((Fintype.equivFin (E →+* ℂ)).symm.injective (Sigma.mk.inj h).1).symm

theorem rt0_conj_neg_ne_zero : starRingEnd ℂ H.rt0 ≠ H.rt0 := by
  intro h2
  have him : H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h2
  have h3 := congrArg Complex.re H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  simp [pow_two, him] at h3
  nlinarith [mul_self_nonneg H.rt0.re]

theorem conj_ne {τ : E →+* ℂ} (h : τ (H.rt : E) = H.rt0) : conjEmb τ (H.rt : E) ≠ H.rt0 := by
  intro h1
  exact rt0_conj_neg_ne_zero (H := H) (by simpa [conjEmb, h] using h1)

theorem conj_eq {τ : E →+* ℂ} (h : τ (H.rt : E) ≠ H.rt0) : conjEmb τ (H.rt : E) = H.rt0 := by
  have h0 : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  have h1 : τ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, h0, H.sqrt_neg_disc_sq]; simp
  have h2 : τ (H.rt : E) = -H.rt0 := (sq_eq_sq_iff_eq_or_eq_neg.1 h1).resolve_left h
  have h3 : starRingEnd ℂ H.rt0 ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, H.sqrt_neg_disc_sq]; simp
  have h4 : starRingEnd ℂ H.rt0 = -H.rt0 := (sq_eq_sq_iff_eq_or_eq_neg.1 h3).resolve_left rt0_conj_neg_ne_zero
  simp [conjEmb, h2, h4]

theorem mult_add (τ : E →+* ℂ) : Dw.mult τ + Dw.mult (conjEmb τ) = Dw.p + Dw.q := by
  unfold Datum.mult
  by_cases h : τ (H.rt : E) = H.rt0
  · rw [if_pos h, if_neg (conj_ne h)]
  · rw [if_neg h, if_pos (conj_eq h), add_comm]

theorem two_mul_length : 2 * (letters Dw).length = Module.finrank ℚ E * (Dw.p + Dw.q) := by
  classical
  have h1 : (letters Dw).length = ∑ τ, Dw.mult τ := by
    rw [← List.toFinset_card_of_nodup (nodup_letters Dw),
      Finset.eq_univ_of_forall fun x => List.mem_toFinset.2 (mem_letters Dw x), Finset.card_univ, Fintype.card_sigma]
    simp
  have hinv : Function.Involutive (conjEmb : (E →+* ℂ) → (E →+* ℂ)) := fun τ => by
    ext x; simp [conjEmb]
  have h2 : ∑ τ, Dw.mult (conjEmb τ) = ∑ τ, Dw.mult τ := hinv.bijective.sum_comp Dw.mult
  rw [h1, two_mul]
  nth_rewrite 2 [← h2]
  rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun τ _ => mult_add Dw τ, Finset.sum_const, Finset.card_univ,
    Embeddings.card, smul_eq_mul]

end Free

theorem finrank_host (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := D.host.finrank_E'

theorem letters_spec : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ), (letters S.Dw).length = D.R.f * N ∧ (letters S.Dw).Nodup ∧ (∀ x, x ∈ letters S.Dw) ∧ ∀ t : D.what₂.Tau, S.Dw.mult (DV.tauEmb D t) = j ∧ S.Dw.mult (conjEmb (DV.tauEmb D t)) = N - j := by
  intro D A N j S _ _
  refine ⟨?_, nodup_letters _, mem_letters _, fun t => ⟨?_, ?_⟩⟩
  · have h := two_mul_length S.Dw
    rw [finrank_host, S.rank_eq, mul_assoc] at h
    omega
  · rw [Datum.mult, if_pos (A.cm t), S.p_eq]
  · rw [Datum.mult, if_neg (conj_ne (A.cm t))]
    have := S.p_eq
    have := S.rank_eq
    omega

end GlobalTheory.Proof.LetterConjugation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevIsReadsTw
section
noncomputable section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TypeLev Matrix GlobalTheory.EX
open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.SeeSaw.TopLevel

namespace GlobalTheory.SeeSaw.TwLev

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cl_nonempty {B : Base} {X : PreX B.toPre} (I : TC B X) (a : I.ι) : Nonempty (I.stX a).Cl := by
  haveI : NeZero (B.R.N B.R.m - 1) := ⟨by
    have := Formalism.L2.Col.rank_X'_eq B.R; have := B.R.m_add_three_le_k; unfold Ranks.r at *; omega⟩
  exact ⟨⟨(), Quotient.mk _ ⟨(DecoF.base _ _ _ _ _, ∅), Set.mem_singleton _⟩⟩⟩

theorem q_inj {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (a : I.ι) :
    ∀ P P' : I.Q a, underPl B.host.F P.1 = underPl B.host.F P'.1 → P = P' := by
  classical
  intro P P' e
  rcases (GlobalTheory.Mem.Col2.under_eq_iff B.host P.1 P'.1).1 (HeightOneSpectrum.ext (congrArg HeightOneSpectrum.asIdeal e.symm)) with h | h
  · exact Subtype.ext h.symm
  · exact absurd (h ▸ Finset.mem_union_right _ (GlobalTheory.Mem.Col2.ChEx.q_sub_SQ I a P'.2))
      ((GlobalTheory.Mem.LevTwist.levOk_twists B X I hOk).1.split P.1 (Finset.mem_union_right _ (GlobalTheory.Mem.Col2.ChEx.q_sub_SQ I a P.2)))

set_option maxHeartbeats 2000000 in

theorem levIs_reads_tw : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (hPins : TC.Pins B X) (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (a : I.ι) (ha : a ≠ I.mu0) {bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))}
    (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramP (I.rec7 l Z)) 1 (I.rec7 l Z).R.f bad)
    {y lat st}
    (hO : letI := Formalism.BasicNotions.tensTopL (F := (I.rec7 l Z).host.F) (E := (I.rec7 l Z).host.E) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F);
      ∀ᶠ (u : GL (Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1)) (TensorProduct (I.rec7 l Z).host.F (I.rec7 l Z).host.E (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F))) in nhds 1,
        ∀ κ : S.U, κ.1 = u → S.chi κ = 1)
    (hK : I.ReadsP a S.Lb S.U S.chi y lat st)
    (P' : LevelP (B.primes X).vGs B.R.r ℂ) (hH : ∀ g, g ∈ P'.H ↔ ∀ w, g w ∈ (I.Ps w).H)
    (hchi : ∀ (g : P'.H) (hg : ∀ w, g.1 w ∈ (I.Ps w).H),
      ((P'.chi g : ℂˣ) : ℂ) = ∏ w, B.embLL (((I.Ps w).lam ⟨g.1 w, hg w⟩ : B.LLˣ) : B.LL))
    (cg : ℕ → ∀ PP : Pl (I.rec7 l Z).host.E, (kP PP)ˣ →* ℂˣ)
    (hcg : ∀ c (w : (B.primes X).vGs) x, ((cg (c + 1) w.1 x : ℂˣ) : ℂ) = B.embLL ((Formalism.L2.Col.chiAt I.Ch w c x : B.LLˣ) : B.LL))
    (ξ : ∀ PP : Pl (I.rec7 l Z).host.E, (kP PP)ˣ →* ℂˣ)
    (hξ : ∀ PP ∈ I.Q a, ∀ x, ((ξ PP x : ℂˣ) : ℂ) =
      B.embLL ((Formalism.L2.DIV.resChar (I.tup a : Formalism.L2.DIV.Chr B.fields.F B.fields.E B.fields.K) PP x : B.LLˣ) : B.LL))
    (hr : B.R.r ≤ (I.rec7 l Z).sp.X'.rank),
    LevIs S (levS _ 1 (Lev.datY (I.rec7 l Z).sp.X'.rank B.R.r B.R.t B.R.m hr (B.primes X).vGs (I.Q a) P' cg ξ Lev.Frm.B))
      (Lev.levChi _ 1 (Lev.datY (I.rec7 l Z).sp.X'.rank B.R.r B.R.t B.R.m hr (B.primes X).vGs (I.Q a) P' cg ξ Lev.Frm.B)) := by
  intro B X I hOk hPins l Z a ha bad S y lat st hO hK P' hH hchi cg hcg ξ hξ hr
  obtain ⟨-, gP, -, -⟩ := GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hOk hPins l Z
  have gX : (I.rec7 l Z).sp.X'.gram = 1 := by
    have := congrArg (Matrix.reindex (finCongr (rankP (I.rec7 l Z))) (finCongr (rankP (I.rec7 l Z)))).symm gP
    rw [gramP, Equiv.symm_apply_apply] at this
    rw [this, Matrix.reindex_symm, Matrix.reindex_apply, Matrix.submatrix_one_equiv]
  haveI : NeZero (B.R.N B.R.m - 1) := ⟨by
    have := Formalism.L2.Col.rank_X'_eq B.R; have := B.R.m_add_three_le_k; unfold Ranks.r at *; omega⟩
  have hLb : S.Lb = Formalism.L2.Col.stdLat B.fields.E (B.R.N B.R.m - 1) := by
    ext x
    refine (hK.lb x).trans (Iff.trans ?_ (Formalism.L2.Col.mem_stdLat x).symm)
    exact forall_congr' fun j => ⟨fun ⟨r, h, _⟩ => ⟨r, h.symm⟩, fun ⟨r, h⟩ => ⟨r, h.symm, fun _ => one_dvd _⟩⟩
  obtain ⟨c⟩ := cl_nonempty I a
  have hR := GlobalTheory.T.levelReading_rationalAtTwist_extends_integralUnitary (Q := I.Q a) B.sp.cm gP S (rowTyG I.Ch I.Ps) B.embLL _ _ (GlobalTheory.Mem.Col2.ChEx.q_conj I hOk a)
    (q_inj I hOk a) hO (GlobalTheory.T.twistedTuple_reading_level_character I hOk hPins l Z a S hK c ξ hξ)
  have key := @GlobalTheory.T.twistPrimeLevel_iff_reductionLevel_conjugateCharacter B.fields.F B.fields.E B.fields.K _ _ _ _ (GlobalTheory.Mem.Col2.starE B) _ _ B.sp.cm (B.R.N B.R.m - 1) _
    (rankP (I.rec7 l Z)) _ _ _ gX gP _ _ _ S hLb B.R.r B.R.t B.R.m (Formalism.L2.Col.r_le_X' B.R) hr
    (Formalism.L2.Col.t_pos B.R) (Formalism.L2.Col.rank_X'_eq B.R) (B.primes X).vGs (I.Q a) I.Ps (Formalism.L2.Col.chiAt I.Ch) B.embLL ξ hR
    P' cg hH hchi hcg
  show (∀ h, h ∈ levS _ 1 _ ↔ _) ∧ _
  refine ⟨fun h => ⟨fun hh => ?_, fun ⟨κ, h1, h2⟩ => ⟨h1, (key _ κ.1 h2).1.2 κ.2⟩⟩, fun h κ hκ => (key _ κ.1 hκ.2).2 κ.2⟩
  obtain ⟨y, hy⟩ := exists_copy (rankP (I.rec7 l Z)) (Lev.finE (I.rec7 l Z).sp.X' h)
  exact ⟨⟨y, (key _ y hy).1.1 hh.2⟩, hh.1, hy⟩

end GlobalTheory.SeeSaw.TwLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameCoordinatesComp
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.CoordComp

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FactorDepth

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)

open MonObj in

theorem comb_map {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') {x : Sp S ⟶ X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} {cf : Fin m → S} {w : Sp (DualNumber S) ⟶ t.G.left}
    (h : IsCombAtG t x v cf w) :
    IsCombAtG t (spMap φ ≫ x) (fun i => spMap (dualMap φ) ≫ v i) (fun i => φ (cf i)) (spMap (dualMap φ) ≫ w) := by
  obtain ⟨u, hu, rfl⟩ := h
  let δ : tEpsG (spMap φ ≫ x) ⟶ tEpsG x := Over.homMk (spMap (dualMap φ)) (by
    show spMap (dualMap φ) ≫ spMap (algebraMap S (DualNumber S)) ≫ x =
      spMap (algebraMap S' (DualNumber S')) ≫ spMap φ ≫ x
    rw [← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', dualMap_comp_alg])
  refine ⟨fun i => δ ≫ u i, fun i => ?_, ?_⟩
  · simp only [Over.comp_left, δ, Over.homMk_left]
    rw [hu i, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', dualMap_comp_epsMul]
  · rw [List.prod_ofFn, List.prod_ofFn, ← comp_prodT]
    rfl

theorem comb_comb {S : Type} [CommRing S] [IsLocalRing S] {x : Sp S ⟶ X} {m n : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} (hv : ∀ j, IsTanAtG t x (v j))
    {w : Fin n → (Sp (DualNumber S) ⟶ t.G.left)} (hw : ∀ j, IsTanAtG t x (w j))
    {u : Sp (DualNumber S) ⟶ t.G.left} (hu : IsTanAtG t x u) (B : Fin n → Fin m → S) (a : Fin n → S)
    (h1 : ∀ i, IsCombAtG t x v (B i) (w i)) (h2 : IsCombAtG t x w a u) :
    IsCombAtG t x v (fun k => ∑ j, a j * B j k) u := by
  obtain ⟨d, xc, hx⟩ := GlobalTheory.ShFam.EigLoc.exists_chart t x
  choose p hp using fun j => GlobalTheory.LieLocBasis.vec_exists hx _ (hv j)
  choose q hq using fun j => GlobalTheory.LieLocBasis.vec_exists hx _ (hw j)
  obtain ⟨r, rfl⟩ := GlobalTheory.LieLocBasis.vec_exists hx _ hu
  obtain rfl : v = _ := funext hp
  obtain rfl : w = _ := funext hq
  simp only [GlobalTheory.LieLocBasis.comb_iff hx] at h1 h2 ⊢
  rw [h2]
  simp only [h1, Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

theorem spMap_comp2 {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) :
    spMap (ψ.comp φ) = spMap ψ ≫ spMap φ := (spMap_comp' _ _).symm

theorem dualMap_comp2 {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) :
    dualMap (ψ.comp φ) = (dualMap ψ).comp (dualMap φ) :=
  RingHom.ext fun x => by ext <;> simp [dualMap]

end GlobalTheory.ShFam.CoordComp

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle GlobalTheory.ShFam.CoordComp in

theorem GlobalTheory.ShFam.CoordComp.coord_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (R : Type) [CommRing R] (φ : c.F →+* R) (x : Sp R ⟶ Z.X) (f : EigFrame Z φ x) (R' : Type) [CommRing R'] (φ' : c.F →+* R') (x' : Sp R' ⟶ Z.X) (g : EigFrame Z φ' x') (R'' : Type) [CommRing R''] (φ'' : c.F →+* R'') (x'' : Sp R'' ⟶ Z.X) (h : EigFrame Z φ'' x'') (ψ : R →+* R') (ψ' : R' →+* R'') (A : Mat Dw.mult R') (A' : Mat Dw.mult R''), IsLocalRing R'' → f.Coord ψ g A → g.Coord ψ' h A' → f.Coord (ψ'.comp ψ) h (A' * A.map ψ') := by
  intro E _ _ _ H Dw l Xo c O _ β Z R _ φ x f R' _ φ' x' g R'' _ φ'' x'' h ψ ψ' A A' hl ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩
  subst a1 a2 b1 b2
  refine ⟨by rw [spMap_comp2, Category.assoc], rfl, fun τ i => ?_⟩
  have e : (fun k => spMap (dualMap (ψ'.comp ψ)) ≫ f.v τ k) =
      fun k => spMap (dualMap ψ') ≫ spMap (dualMap ψ) ≫ f.v τ k :=
    funext fun k => by rw [dualMap_comp2, spMap_comp2, Category.assoc]
  rw [e]
  exact comb_comb Z.t
    (fun j => GlobalTheory.FactorDepth.isTanAtG_map _ ψ' (GlobalTheory.FactorDepth.isTanAtG_map _ ψ (f.tan τ j)))
    (fun j => GlobalTheory.FactorDepth.isTanAtG_map _ ψ' (g.tan τ j)) (h.tan τ i) (fun j k => ψ' (A τ j k)) (A' τ i)
    (fun j => comb_map Z.t ψ' (a3 τ j)) (b3 τ i)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameCoordinatesUniqueInvertible
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.EigCoord

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LieLocBasis GlobalTheory.ShFam.EigLoc GlobalTheory.FlagBundle
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (IsUnivChart sp)

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X} {n : ℕ}
  {xc : ∀ m : ℕ, sp (R₀ := R) (ReciprocityTheory.ChartRestriction.G.Chart.JetR R (Fin n) m) ⟶ (Over.pullback x).obj Z.t.G}

theorem exists_basis (hx : IsUnivChart _ n xc) (g : EigFrame Z φ x) (τ : E →+* ℂ) :
    ∃ B : Module.Basis (Fin (Dw.mult τ)) R (eig c φ hx τ), ∀ i, g.v τ i = vec Z.t x xc (B i) := by
  choose e he using fun i => vec_exists hx (g.v τ i) (g.tan τ i)
  have hm : ∀ i, e i ∈ eig c φ hx τ := fun i => (vec_eig_iff hx _ _).1 (by rw [← he i]; exact g.eig τ i)
  let b : Fin (Dw.mult τ) → eig c φ hx τ := fun i => ⟨e i, hm i⟩
  have key : ∀ w : eig c φ hx τ, ∃! a : Fin (Dw.mult τ) → R, ∑ j, a j • b j = w := fun w => by
    have h := g.basis τ (vec Z.t x xc w) (vec_tan hx _) ((vec_eig_iff hx _ _).2 w.2)
    rw [show g.v τ = fun j => vec Z.t x xc (e j) from funext he] at h
    simp only [comb_iff hx] at h
    refine (existsUnique_congr fun a => ?_).1 h
    rw [Subtype.ext_iff, eq_comm]
    simp [b]
  have li : LinearIndependent R b := Fintype.linearIndependent_iff.2 fun a ha i =>
    congrFun ((key 0).unique ha (show ∑ j, (0 : Fin (Dw.mult τ) → R) j • b j = 0 by simp)) i
  have sp' : ⊤ ≤ Submodule.span R (Set.range b) := fun w _ =>
    (Submodule.mem_span_range_iff_exists_fun R).2 (key w).exists
  exact ⟨Module.Basis.mk li sp', fun i => by rw [Module.Basis.mk_apply]; exact he i⟩

theorem exists_frame (hx : IsUnivChart _ n xc) (B : ∀ τ, Module.Basis (Fin (Dw.mult τ)) R (eig c φ hx τ)) :
    ∃ g : EigFrame Z φ x, ∀ τ i, g.v τ i = vec Z.t x xc (B τ i) := by
  refine ⟨⟨fun τ i => vec Z.t x xc (B τ i), fun τ i => vec_tan hx _, fun τ i => (vec_eig_iff hx _ _).2 (B τ i).2,
    fun τ w hw he => ?_⟩, fun _ _ => rfl⟩
  obtain ⟨cc, rfl⟩ := vec_exists hx w hw
  let v : eig c φ hx τ := ⟨cc, (vec_eig_iff hx _ _).1 he⟩
  have k : ∀ a, IsCombAtG Z.t x (fun i => vec Z.t x xc (B τ i)) a (vec Z.t x xc cc) ↔ (B τ).equivFun v = a := fun a => by
    rw [comb_iff hx, ← LinearEquiv.eq_symm_apply, Module.Basis.equivFun_symm_apply, Subtype.ext_iff]
    simp [v]
  simp only [k]
  exact existsUnique_eq'

theorem exists_basis_of_isUnit {M ι : Type} [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]
    (B : Module.Basis ι R M) (A : Matrix ι ι R) (h : IsUnit A.det) :
    ∃ B' : Module.Basis ι R M, ∀ i, B' i = ∑ j, A i j • B j := by
  refine ⟨B.map (Matrix.toLinearEquiv B A.transpose (by rwa [Matrix.det_transpose])), fun i => ?_⟩
  simp [Matrix.toLin_self]

theorem isUnit_det_of_basis {M ι : Type} [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]
    (B B' : Module.Basis ι R M) (A : Matrix ι ι R) (h : ∀ i, B' i = ∑ j, A i j • B j) : IsUnit A.det := by
  have e : A = (B.toMatrix B').transpose := by
    ext i j
    rw [Matrix.transpose_apply, Module.Basis.toMatrix_apply, h i, Module.Basis.repr_sum_self]
  rw [e, Matrix.det_transpose]
  exact B.isUnit_det B'

end GlobalTheory.ShFam.EigCoord

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
  GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle GlobalTheory.ShFam.EigLoc GlobalTheory.ShFam.EigCoord GlobalTheory.LieLocBasis in

theorem GlobalTheory.ShFam.EigCoord.coord_spec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (R : Type) [CommRing R] (φ : c.F →+* R) (x : Sp R ⟶ Z.X) (f : EigFrame Z φ x) (R' : Type) [CommRing R'] (φ' : c.F →+* R') (x' : Sp R' ⟶ Z.X) (ψ : R →+* R'), IsLocalRing R' → f.Stable → x' = spMap ψ ≫ x → φ' = ψ.comp φ → (∀ g : EigFrame Z φ' x', (∃! A : Mat Dw.mult R', f.Coord ψ g A) ∧ ∀ A, f.Coord ψ g A → ∀ τ, IsUnit (A τ).det) ∧ ∀ A : Mat Dw.mult R', (∀ τ, IsUnit (A τ).det) → ∃ g : EigFrame Z φ' x', f.Coord ψ g A := by
  intro E _ _ _ H Dw l Xo c O _ β Z R _ φ x f R' _ φ' x' ψ _ hf hx' hφ'
  subst hx' hφ'
  obtain ⟨g₀, hg₀⟩ := hf R' ψ
  obtain ⟨n, xc, hx⟩ := exists_chart Z.t (spMap ψ ≫ x)
  choose B₀ hB₀ using exists_basis hx g₀
  have hv : ∀ τ, (fun k => spMap (dualMap ψ) ≫ f.v τ k) = g₀.v τ := fun τ => funext fun k => (hg₀ τ k).symm
  have key : ∀ (g : EigFrame Z (ψ.comp φ) (spMap ψ ≫ x))
      (B : ∀ τ, Module.Basis (Fin (Dw.mult τ)) R' (eig c (ψ.comp φ) hx τ)),
      (∀ τ i, g.v τ i = vec Z.t _ xc (B τ i)) → ∀ A : Mat Dw.mult R',
        f.Coord ψ g A ↔ ∀ τ i, B τ i = ∑ j, A τ i j • B₀ τ j := fun g B hB A => by
    simp only [EigFrame.Coord, true_and]
    refine forall_congr' fun τ => forall_congr' fun i => ?_
    rw [hv, hB, show g₀.v τ = fun j => vec Z.t _ xc (B₀ τ j) from funext (hB₀ τ), comb_iff hx, Subtype.ext_iff]
    simp
  refine ⟨fun g => ⟨?_, fun A hA τ => ?_⟩, fun A hA => ?_⟩
  · choose A hA hu using fun τ i => g₀.basis τ (g.v τ i) (g.tan τ i) (g.eig τ i)
    refine ⟨A, ⟨rfl, rfl, fun τ i => by rw [hv]; exact hA τ i⟩, fun A' hA' => ?_⟩
    funext τ i
    exact hu τ i _ (by have := hA'.2.2 τ i; rwa [hv] at this)
  · choose B hB using exists_basis hx g
    exact isUnit_det_of_basis (B₀ τ) (B τ) (A τ) ((key g B hB A).1 hA τ)
  · choose B hB using fun τ => exists_basis_of_isUnit (B₀ τ) (A τ) (hA τ)
    obtain ⟨g, hg⟩ := exists_frame hx B
    exact ⟨g, (key g B hg A).2 hB⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameStableOfIsLocalRing
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.EigStable

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory.LieLocBasis GlobalTheory.ShFam.EigLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (tvec tmap eigLat IsUnivChart scaleD sp)

attribute [local instance] Over.cartesianMonoidalCategory

theorem basis_fixed_bc {L k : Type} [CommRing L] [CommRing k] (ψ : L →+* k) {n m : ℕ}
    (P : Module.End L (Fin n → L)) (P' : Module.End k (Fin n → k)) (hP : ∀ c, P (P c) = P c)
    (h : ∀ c, P' (ψ ∘ c) = ψ ∘ P c) (e : Fin m → Fin n → L) (he : ∀ i, P (e i) = e i)
    (hb : ∀ c, P c = c → ∃! a : Fin m → L, c = ∑ i, a i • e i) (c' : Fin n → k) (hc : P' c' = c') :
    ∃! a : Fin m → k, c' = ∑ i, a i • (ψ ∘ e i) := by
  classical
  choose M hM using fun j : Fin n => (hb _ (hP (Pi.single j 1))).exists
  have hs : ∀ {R : Type} [CommRing R] (a : Fin n → R), ∑ j, a j • (Pi.single j 1 : Fin n → R) = a := fun a => by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hinv : ∀ i, (fun i' => ∑ j, e i j * M j i') = Pi.single i 1 := fun i => by
    refine (hb _ (he i)).unique ?_ ?_
    · conv_lhs => rw [← he i, ← hs (e i), map_sum]
      simp only [map_smul, hM, Finset.smul_sum, Finset.sum_smul, smul_smul]
      exact Finset.sum_comm
    · simp [Pi.single_apply]
  have h1 : ∀ j, P' (Pi.single j 1) = ∑ i, ψ (M j i) • (ψ ∘ e i) := fun j => by
    rw [show (Pi.single j 1 : Fin n → k) = ψ ∘ Pi.single j 1 from funext fun j' => by
      by_cases hj : j' = j <;> simp [hj, Pi.single_apply], h, hM]
    funext r
    simp [Finset.sum_apply]
  refine ⟨fun i => ∑ j, c' j * ψ (M j i), ?_, fun a ha => ?_⟩
  · show c' = _
    conv_lhs => rw [← hc, ← hs c', map_sum]
    simp only [map_smul, h1, Finset.smul_sum, Finset.sum_smul, smul_smul]
    exact Finset.sum_comm
  · funext i
    have h2 : ∀ i', ∑ j, ψ (e i' j) * ψ (M j i) = if i = i' then 1 else 0 := fun i' => by
      have := congrArg ψ (congrFun (hinv i') i)
      simpa [Pi.single_apply, apply_ite ψ] using this
    have h3 : ∀ j, c' j = ∑ i', a i' * ψ (e i' j) := fun j => by
      have := congrFun ha j
      simpa [Finset.sum_apply] using this
    show a i = ∑ j, c' j * ψ (M j i)
    simp only [h3, Finset.sum_mul, _root_.mul_assoc]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, h2]
    simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {l : Level H} (c : Coeff l)

theorem exists_proj_bc {L : Type} [CommRing L] [IsLocalRing L] (φ : c.F →+* L) {x : Sp L ⟶ X} {n : ℕ}
    {xc : ∀ m : ℕ, sp (R₀ := L) (ReciprocityTheory.ChartRestriction.G.Chart.JetR L (Fin n) m) ⟶ (Over.pullback x).obj t.G} (hx : IsUnivChart _ n xc)
    {k : Type} [CommRing k] (ψ : L →+* k) :
    ∃ (xc' : ∀ m : ℕ, sp (R₀ := k) (ReciprocityTheory.ChartRestriction.G.Chart.JetR k (Fin n) m) ⟶ (Over.pullback (spMap ψ ≫ x)).obj t.G)
      (hx' : IsUnivChart _ n xc'),
      (∀ cc : Fin n → L, vec t (spMap ψ ≫ x) xc' (ψ ∘ cc) = spMap (dualMap ψ) ≫ vec t x xc cc) ∧
      ∀ τ, ∃ (P : Module.End L (Fin n → L)) (P' : Module.End k (Fin n → k)), (∀ cc, P (P cc) = P cc) ∧
        (∀ cc, P' (ψ ∘ cc) = ψ ∘ P cc) ∧ (∀ cc, P cc = cc ↔ cc ∈ eig c φ hx τ) ∧
        ∀ cc, P' cc = cc ↔ cc ∈ eig c (ψ.comp φ) hx' τ := by
  classical
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨α, hinj, ⟨f, hf, hfs⟩, hN⟩ :=
    exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
  have key : ∀ (τ : E →+* ℂ) {R : Type} [CommRing R] [Algebra c.F R] {x : Sp R ⟶ X}
      {xc : ∀ m : ℕ, sp (R₀ := R) (ReciprocityTheory.ChartRestriction.G.Chart.JetR R (Fin n) m) ⟶ (Over.pullback x).obj t.G}
      (hx : IsUnivChart _ n xc), (∀ m, proj (rho hx) (embK c) α τ (proj (rho hx) (embK c) α τ m) =
          proj (rho hx) (embK c) α τ m) ∧
        ∀ m, proj (rho hx) (embK c) α τ m = m ↔ m ∈ eig c (algebraMap c.F R) hx τ :=
    fun τ {R} _ _ {x xc} hx => by
      have e₁ : ∀ m, ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV (rho hx) (embK c τ) (proj (rho hx) (embK c) α τ m) := fun m =>
        eig_of_alpha _ _ α hN τ (proj_eig_alpha _ _ α hinj f hf hfs τ m)
      have e₂ : ∀ m, ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV (rho hx) (embK c τ) m → proj (rho hx) (embK c) α τ m = m := fun m hm => by
        have := proj_sum_eig (rho hx) (embK c) α hinj (Pi.single τ m) (fun τ' => by
          by_cases h : τ' = τ
          · subst h; rwa [Pi.single_eq_same]
          · rw [Pi.single_eq_of_ne h]; intro a; simp) τ
        rwa [Finset.sum_pi_single', if_pos (Finset.mem_univ _), Pi.single_eq_same] at this
      refine ⟨fun m => e₂ _ (e₁ m), fun m => ?_⟩
      rw [ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff]
      exact ⟨fun h => h ▸ e₁ m, fun h => e₂ m h⟩
  letI : Algebra c.F L := φ.toAlgebra
  letI : Algebra L k := ψ.toAlgebra
  letI : Algebra c.F k := (ψ.comp φ).toAlgebra
  obtain ⟨xc', hx', hv⟩ := vec_bc (S' := k) hx
  have htm : ∀ (a : 𝓞 E) (cc : Fin n → L), rho hx' a (algebraMap L k ∘ cc) = algebraMap L k ∘ rho hx a cc :=
    fun a cc => vec_inj hx' (by
      show vec t _ xc' (tmap hx' _ _) = vec t _ xc' (_ ∘ tmap hx _ _)
      rw [vec_tmap hx', hv, hv, vec_tmap hx, Category.assoc])
  have pw : ∀ (j : ℕ) cc, (rho hx' α ^ j) (algebraMap L k ∘ cc) = algebraMap L k ∘ (rho hx α ^ j) cc := fun j => by
    induction j with
    | zero => exact fun _ => rfl
    | succ j ih => intro cc; rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih]; exact htm α _
  have pr : ∀ (Q : Polynomial c.F) cc, Polynomial.aeval (rho hx' α) (Q.map (algebraMap c.F k)) (algebraMap L k ∘ cc) =
      algebraMap L k ∘ Polynomial.aeval (rho hx α) (Q.map (algebraMap c.F L)) cc := fun Q cc => by
    induction Q using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [Polynomial.map_add, Polynomial.map_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hp, hq]
      funext j; simp
    | monomial j a =>
      rw [Polynomial.map_monomial, Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial,
        Module.End.mul_apply, Module.End.mul_apply, pw, Module.algebraMap_end_apply, Module.algebraMap_end_apply]
      funext i
      exact (map_mul (algebraMap L k) _ _).symm
  exact ⟨xc', hx', hv, fun τ => ⟨_, _, (key τ hx).1, pr _, (key τ hx).2, (key τ hx').2⟩⟩

end GlobalTheory.ShFam.EigStable

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
  GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle GlobalTheory.ShFam.EigLoc GlobalTheory.LieLocBasis in

theorem GlobalTheory.ShFam.EigStable.stable_of_isLocalRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (R : Type) [CommRing R] (φ : c.F →+* R) (x : Sp R ⟶ Z.X) (f : EigFrame Z φ x), IsLocalRing R → f.Stable := by
  intro E _ _ _ H Dw l Xo c O _ β Z R _ φ x f _ R' _ _ ψ
  obtain ⟨n, xc, hx⟩ := exists_chart Z.t x
  obtain ⟨xc', hx', hv, hP⟩ := GlobalTheory.ShFam.EigStable.exists_proj_bc c φ hx ψ
  choose e he using fun τ i => vec_exists hx (f.v τ i) (f.tan τ i)
  choose P P' hPP hc hP hP' using hP
  have heig : ∀ τ i, P τ (e τ i) = e τ i := fun τ i =>
    (hP τ _).2 ((vec_eig_iff hx _ _).1 (by rw [← he]; exact f.eig τ i))
  have hfv : ∀ τ, f.v τ = fun i => vec Z.t x xc (e τ i) := fun τ => funext (he τ)
  refine ⟨⟨fun τ i => vec Z.t (spMap ψ ≫ x) xc' (ψ ∘ e τ i), fun τ i => vec_tan hx' _,
    fun τ i => (vec_eig_iff hx' _ _).2 ((hP' τ _).1 (by rw [hc, heig])), fun τ w hw hw' => ?_⟩,
    fun τ i => by rw [he]; exact hv _⟩
  obtain ⟨cc, rfl⟩ := vec_exists hx' w hw
  simp only [comb_iff hx']
  refine GlobalTheory.ShFam.EigStable.basis_fixed_bc ψ (P τ) (P' τ) (hPP τ) (hc τ) (e τ) (heig τ) (fun c₀ h₀ => ?_) cc
    ((hP' τ _).2 ((vec_eig_iff hx' _ _).1 hw'))
  have := f.basis τ _ (vec_tan hx c₀) ((vec_eig_iff hx _ _).2 ((hP τ _).1 h₀))
  rw [hfv] at this
  simpa only [comb_iff hx] using this
end
end

