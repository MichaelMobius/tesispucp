# Mapa de dependencias matemáticas — novena etapa

## Estructura variacional y cobertura

Las declaraciones nuevas están en `DensidadResidualMinima.lean`, `VariacionalPINN.lean` y `CoberturaPINN.lean`. Conservan los teoremas de la octava etapa.

| Paso | Declaración | Estado lógico |
|---|---|---|
| Densidad medible `ρ≥ρ₀>0` casi en todas partes, sin `ρMax` | `DensidadInferior`, `ResiduoPonderadoIntegrable` | La integrabilidad ponderada del **residuo particular** es hipótesis explícita; de `r∈L²` y solo `ρ≥ρ₀` no se deduce |
| Comparación ponderada y cota H¹ sin `ρMax` | `cota_densidad_sin_superior`, `cota_perdida_sin_superior`, `estimacion_error_sin_superior` | **Probadas** bajo integrabilidad ponderada y dominación de la pérdida, además de las hipótesis energéticas previas |
| Pérdida empírica interior/frontera, pérdida poblacional, regularización | `ProblemaPINN`, `perdidaEmpirica`, `perdidaPoblacional`, `funcionalRegularizado` | Definiciones separadas de (3.22); medidas de probabilidad, tamaños positivos, pesos residuales positivos; regularizadores son cuadrados de valores de seminorma parametrizados |
| Comparación de minimizador con cualquier comparador admisible | `EsMinimizadorGlobal`, `comparacion_global` | **Probada**; la existencia del minimizador es una premisa |
| Interpolador exacto (3.24), pesos iguales (3.23), cota uniforme de regularidad (3.25) | `ComparadorExacto`, `funcional_pesos_iguales`, `perdidaEmpirica_le_regularidad_uniforme` | **Probadas las implicaciones** `R(hm)≤R(gm)` y `LossEmp(hm)≤a_m R*`; existencia y uniformidad de comparadores siguen como premisas |
| Paso puntual de cobertura (3.14) | `residuo_puntual_de_cobertura` | **Probado** bajo cobertura y cotas Hölder de operador y dato |
| Geometría, masa de bolas (3.4), pesos (3.7)/(3.23), objetivo integral (3.13) | `MuestrasCubren`, `MasaBolaSuperior`, `factorCoberturaCuadrado`, `pesoCobertura`, `pesoRegularizacionIgual`, `ObjetivoCoberturaIntegral` | Geometría y desigualdad integral están **formuladas**, no demostradas; falta Voronoi medible, control de masa de celdas e integración |

**Densidad y (3.4).** Matemáticamente, en el cuadrado, la cota `μr(B̄(x,r)∩U)≤Cr r²` junto con `dμr=ρr dx`, `ρr∈L¹(U)` y diferenciación de Lebesgue implica `ρr≤Cr/π` casi en todas partes: para casi todo `x∈U`, tomar `r<dist(x,∂U)` y pasar al límite en las medias sobre `B̄(x,r)`, cuyo volumen es `πr²`. Esa implicación **aún no es un teorema Lean**. El puente pendiente es especializar `IsUnifLocDoublingMeasure.ae_tendsto_average` a bolas de Lebesgue en `ℝ²`, convertir la cota de masa en cota de medias y usar `volume_closedBall`. La nueva comparación ponderada evita necesitar ese puente para residuos con integral ponderada finita.

**Cadena para (3.26):** minimalidad + comparador exacto + regularidad uniforme ⇒ `LossEmp(hm)≤a_m R*` **probado**; cobertura geométrica + Hölder + cota (3.4) ⇒ desigualdad integral (3.13) **pendiente**; pesos y escalas muestrales + (3.13) ⇒ (3.26) **pendiente**. Para cobertura eventual de probabilidad uno faltan ocupación de celdas i.i.d., unión de eventos, sumabilidad de las probabilidades de fallo a lo largo de `mr(n),mb(n)≥n` y Borel–Cantelli sobre un espacio común. (3.27) requiere además pasar de pérdida poblacional a control `C⁰` mediante masa local y regularidad Hölder; (3.28) requiere las cotas cuantitativas de ese paso. Ninguno de estos resultados estadísticos se declara probado.

El informe de la etapa está en `INFORME_NOVENA_ETAPA.md`. Las secciones históricas siguientes conservan su fecha y alcance originales.

## Pérdida poblacional y transferencia probabilística condicional

`PerdidaPoblacional.lean` trabaja en `U=(-1,1)²`, con `r=Δ(ψq)-f∈L²(U)` y `h=ψq` globalmente suave. La tesis fija `L=Δ`, y sus ecuaciones (3.72)–(3.74) usan el residuo opuesto `f−Δh`, con la misma norma. La constante `K=constanteEnergiaCuadrado>0` es la misma para todos los candidatos y tamaños de muestra.

| Dependencia | Declaración Lean | Resultado y límite |
|---|---|---|
| `r∈L²`, `ρ₀≤ρ≤ρMax` c.t.p., `ρ` medible | `DensidadResidual`, `integrable_residuo_ponderado` | `ρr²∈L¹(U)`; **la cota superior esencial es una premisa adicional explícita**, suficiente para finitud. La Hipótesis 3.2 enuncia la cota inferior y cotas de masa de bolas, no una cota superior directa de `ρ`. |
| Identidad `‖r‖²₂=∫r²` y cota inferior de la densidad | `cota_residuo_por_densidad` | `ρ₀‖r‖²₂≤∫ρr²`, con representantes `Lp` y casi en todas partes |
| `λr>0`, pérdida total que domina `λr∫ρr²` | `perdidaResidualPoblacional_nonneg`, `cota_residuo_por_perdida`, `cota_norma_residuo_por_perdida` | `‖r‖²₂≤Loss/(ρ₀λr)` y su versión con raíz; la dominación es una hipótesis visible que corresponde a los términos no negativos de la pérdida PINN |
| `u*∈H01`, `Δu*=f` distribucional, `h=ψq` suave | `estimacion_error_por_perdida` | `‖h−u*‖H¹≤K(ρ₀λr)^(-1/2)√Loss`, paso ponderado de (3.74) |
| Dominación para cada índice y `Loss_n→0` | `tendsto_psiGraph_de_perdida` | Convergencia `H¹` determinista; el antecedente de pérdida no se deduce de (3.26) aquí |
| `Loss_n≤A·mr(n)^(-α/2)` en dimensión `d=2` | `tasa_error_de_perdida_mr` | Cota `K√A/√(ρ₀λr)·mr(n)^(-α/4)`, exponente de (3.73); `n` y `mr(n)` son distintos y la cota de pérdida es premisa |
| Espacio de probabilidad, dominación y convergencia de pérdida c.t.p. | `tendsto_psiGraph_de_perdida_ae` | Transferencia casi segura trayectoria por trayectoria; no se construye la pérdida aleatoria |
| Pérdida y aproximantes mensurables; evento de pérdida de probabilidad uno | `prob_uno_tendsto_psiGraph_de_perdida` | El evento de convergencia `H¹` es mensurable y tiene probabilidad uno. Las mensurabilidades son hipótesis visibles, no consecuencias de un minimizador aún no construido. |

**Pendiente para los Teoremas 3.8 y 3.20 completos:** formalizar la Hipótesis 3.2 (distribuciones i.i.d., independencia, particiones y cobertura), la Hipótesis 3.7 (comparadores y regularidad uniforme), pesos (3.23), minimizadores globales mensurables y la cota de pérdida (3.26). Los límites `C⁰` (3.27) y tasas (3.28) tampoco se han demostrado. La tasa (3.73) y la convergencia (3.72) son **implicaciones condicionales** en la clase homogénea `ψq`; faltan la construcción aleatoria y el puente de trazas para candidatos generales. La normalización `∫ρ=1` de una densidad probabilística no interviene en la comparación y no se codifica todavía. La cota superior esencial y la mensurabilidad de los aproximantes son obligaciones adicionales explícitas de esta formalización.

Véase `INFORME_OCTAVA_ETAPA.md` para la correspondencia literal con la tesis y la verificación. Las secciones siguientes registran el estado histórico de etapas previas; sus listas de pendientes deben leerse en la fecha de cada etapa.

## Constante uniforme y transferencia determinista

Para `U=(-1,1)²` y la medida de Lebesgue, `constanteEnergiaCuadrado` se elige **una sola vez** a partir de `exists_poincare_constant` y vale `Cₚ√(1+Cₚ²)` para algún `Cₚ>0` dependiente solo del dominio. No se afirma la constante óptima `√2/π` del Corolario 3.23. La prueba de `energia_cuadrado_uniforme` cuantifica primero sobre todos los errores `e∈H01` y todos los residuos `r∈L²(U)` con `Δe=r`; por tanto la elección no depende de `m`, `e` ni `r`.

| Paso | Declaración Lean | Alcance |
|---|---|---|
| `K>0` fija para todo error admisible | `constanteEnergiaCuadrado_pos`, `energia_cuadrado_uniforme` | Forma uniforme del Lema 3.19, ecuación (3.71), en el cuadrado; premisas analíticas `e∈H01`, `Δe=r∈L²` explícitas |
| Residuo de un candidato `h=ψq` ante `u*` fija | `residuoAproximacion`, `laplaciano_error_psi_solucion_exacta` | `r=Δh−f`; requiere `Δu*=f` como ecuación distribucional |
| Cota uniforme para todos los `q` globalmente `C∞` | `estimacion_uniforme_psi_solucion_exacta` | Paso determinista (3.74) en el caso homogéneo, condicionado a `u*∈H01`, `Δu*=f` |
| Cota `‖r_m‖≤ε_m ⇒ ‖h_m−u*‖≤Kε_m` | `cota_error_de_cota_residuo` | Completamente probado bajo esas premisas, con el mismo `K` para todo `m` |
| `r_m→0` en `L²` implica `h_m→u*` en `H¹` | `tendsto_psiGraph_de_residuo_l2` | Implicación determinista previa a (3.72); no demuestra convergencia casi segura del residuo |
| `ε_m→0` y `‖r_m‖≤ε_m` implican convergencia `H¹` | `tendsto_psiGraph_de_cota_residuo` | Probado; la convergencia de `ε_m` es premisa |
| Una tasa residual `A(m+1)^(-β)` se transfiere con coeficiente `KA` | `tasa_potencia_psi` | Transferencia de exponente; no prueba la tasa residual de (3.73) |
| Cota válida en cada realización de un evento arbitrario `A` | `cota_error_en_evento` | Preparación trayectoria por trayectoria; ninguna afirmación sobre la medida de `A` |

**Correspondencia con el Teorema 3.8:** sus hipótesis 3.2 y 3.7, los comparadores exactos, la selección mensurable de minimizadores globales, los pesos de regularización (3.23), la cobertura y la convergencia/tasa de la pérdida poblacional (3.26) no se han formalizado. El enunciado (3.27) proporciona convergencia `C⁰` de `Δh_m−f` casi segura; falta formalizar la transferencia `C⁰→L²` en el evento de probabilidad uno. Para la tasa (3.73) falta además la comparación de la pérdida ponderada con `‖r_m‖²_{L²}` usando `ρ_r≥ρ₀>0` y `λ_r>0`. Por ello (3.72) y (3.73) **no** están demostradas como afirmaciones probabilísticas.

La auditoría de coherencia de las PR #3–#8 se registra en `INFORME_SEPTIMA_ETAPA.md`. Verificación local: `lake build` pasó (3190 trabajos) y `#print axioms` de los teoremas nuevos mostró solo `propext`, `Classical.choice`, `Quot.sound`. El CI Lean 4 / Mathlib de la PR #9 pasó en la ejecución [42561147867](https://github.com/MichaelMobius/tesispucp/actions/runs/42561147867).

## Registro de la sexta etapa

## Residuo laplaciano concreto en `U=(-1,1)²`

La convención de la tesis es `L=Δ`, `Δu*=f` y `r_h=Δh-f` (páginas PDF 113–116, impresas 100–103). La demostración del Teorema 3.20 define `e_m=u*−h_m` y `Δe_m=f−Δh_m`; nuestros teoremas usan `e=h−u*` y `Δe=Δh−f`. Las dos normas son iguales por el signo. La versión `−Δu=f_num` requiere sustituir `f=−f_num`, como aclara la tesis.

| Paso matemático | Declaración Lean nueva | Correspondencia y estado |
|---|---|---|
| `Δf=∂₁²f+∂₂²f` en la base ortonormal de `ℝ²` | `derivadaClásica`, `laplacianoClásico`, `laplacianoClásico_eq_mathlib` | Definición clásica y coincidencia con `Laplacian.laplacian` de Mathlib, probadas |
| `∂ᵢ ofFun(f)=ofFun(∂ᵢf)` dos veces para `f∈C∞` | `derivada_distribucional_clásica`, `segunda_distribucional_clásica` | Probado con `hasWeakFDerivOn_fderiv` de EllipticPDE; fija el signo positivo tras dos derivadas |
| `Δ_distribucional ofFun(f)=ofFun(Δ_clásico f)` | `laplaciano_distribucional_eq_clásico` | Probado para función globalmente `C∞` |
| `Δ_clásico f∈L²(U)` | `laplacianoClásico_suave`, `laplacianoClásico_memLp`, `laplacianoLp`, `laplacianoLp_ae` | Probado por continuidad en la clausura compacta y medida finita del cuadrado |
| `r=Δ(ψq_h−ψq_u)∈L²(U)` | `errorPsi`, `residuoPsi`, `residuoPsi_ae`, `laplaciano_distribucional_errorPsi` | Probado; la diferencia de grafos tiene representante `fnL=ψq_h−ψq_u` casi en todas partes |
| Estimación energética sin premisas `hΔ` ni `he` para dos candidatos suaves `ψq` | `estimacion_psi_suave_residuo_concreto` | **Probado** como instancia determinista de (3.71)/(3.74); usa `psiGraph_mem_H01` de la quinta etapa |
| Candidato `h=ψq`, solución exacta general `u*` con `Δu*=f` | `estimacion_psi_frente_solucion_exacta` | **Condicional** a `u*∈H1Graph.H01` y a la ecuación distribucional; el residuo es `Δh−f` |

La hipótesis `u*∈H01` de la última fila es más fuerte que su pertenencia a `H¹` y su coincidencia de frontera con `h` en el Teorema 3.20. El puente `ker(trace)=H01` no está formalizado. La sexta etapa tampoco formaliza comparadores, minimizadores, muestreo ni tasa probabilística; por tanto **no completa el Teorema 3.20**. Para datos de frontera no homogéneos se necesita además representar una extensión de `g` y probar que el error tiene traza cero. Una penalización finita de frontera no da esta conclusión.

Verificación local: `lake build` (3189 trabajos), `#print axioms` solo `propext`, `Classical.choice`, `Quot.sound`; Lean 4.35.0, Mathlib v4.35.0 y EllipticPDE `c47acceaf985f59e1cf3257ffea077a73ea99dae`. El CI Lean 4 / Mathlib de la PR #8 pasó en la ejecución [42557228273](https://github.com/MichaelMobius/tesispucp/actions/runs/42557228273).

## Registro de la quinta etapa

## Puente nuevo: recorte de `ψ q` y pertenencia a `H₀¹`

Se trabaja exclusivamente en `U=(-1,1)²`, con `ψ(x,y)=(1-x²)(1-y²)` y `q : Plano → ℝ` globalmente `C∞`. La suavidad global es una condición suficiente explícita; el caso de `q` suave solo en un entorno del cuadrado cerrado se reduce a construir una extensión global suave, que aún no está formalizada. No se exige soporte compacto de `q`.

| Dependencia | Declaración Lean | Estado |
|---|---|---|
| Transición suave de EllipticPDE y cota global de su derivada | `Real.smoothTransition`, `EllipticPdes.Extension.exists_bound_deriv_smoothTransition` | Biblioteca fijada |
| Recorte por las cuatro caras, suave y con soporte compacto interior | `lado`, `perfil`, `recorte`, `recortePsiPrueba` | Probado |
| Recorte igual a uno en el cuadrado interior; derivada nula allí | `recorte_uno`, `eventualmente_recorte_valor_y_derivada` | Probado |
| Cota `|Dχδ(x)w| ≤ 4C‖w‖/δ` | `abs_fderiv_recorte_le_norm` | Probado |
| Área exacta de la franja `16δ-16δ²`, y cota `≤16δ` para `0<δ<1/2` | `volumen_real_franja`, `volumen_real_franja_le` | Probado |
| En la franja, `0≤ψ≤4δ`; por cancelación, `‖ψ Dχδ‖≤16C` | `psiCuadrado_le_en_franja`, `norm_psi_smul_fderiv_recorte_le` | Probado |
| Cota uniforme del gradiente de `χδ ψq` a partir de cotas de `q` y `D(ψq)` en el cuadrado cerrado | `existe_cota_q_y_deriv_psi_q`, `norm_fderiv_recortePsi_le` | Probado |
| Convergencia puntual eventual de función y gradiente; convergencia de ambos en `L²(U)` por integrabilidad uniforme y medida finita | `eventualmente_recortePsi_valor_y_gradiente`, `recortePsi_tendsto_fnL`, `recortePsi_tendsto_gradL` | Probado |
| Grafo con representantes `fnL=ψq`, `gradL=∇(ψq)` casi en todas partes | `psiGraph`, `psiGraph_fnL_ae`, `psiGraph_gradL_ae` | Probado |
| `ψq ∈ H1Graph.H01` sin soporte compacto previo de `q` | `psiGraph_mem_H01` | Probado |
| Estimación energética para diferencia de dos candidatos suaves `ψqh-ψqu` | `estimacion_psi_suave_dirichlet_exacto` | **Condicional** a la igualdad distribucional explícita del residuo `Δe=r∈L²` |

La cota de área se ha formalizado como control geométrico de la transición. La prueba de convergencia `L²` utiliza la cota uniforme y la convergencia puntual eventual mediante `unifIntegrable_of` y `tendsto_Lp_finite_of_tendsto_ae`; no usa el valor numérico del área. La cota `ψ≤4δ` sí interviene en la cancelación del término `ψ∇χδ`.

**Pendiente tras la sexta etapa:** extender `q` suave en un entorno del cuadrado cerrado a una función global suave; demostrar `h-u*∈H01` para funciones suaves con valores iguales en toda la frontera sin factorización por `ψ`; tratar `C¹` con mollificación si se necesita preservar la regularidad; y para `H¹` general, formalizar la traza y `ker(trace)=H01` en el cuadrado. La identidad del residuo concreto ya está probada para dos candidatos suaves `ψq` y, condicionalmente a la ecuación de `u*`, para un candidato `ψq` frente a una solución exacta general. Quedan la constante óptima `√2/π` del Corolario 3.23 y las hipótesis PINN y probabilísticas del Teorema 3.20. La penalización finita de frontera sigue siendo un caso distinto.

La auditoría `#print axioms` de los teoremas nuevos contiene solamente `propext`, `Classical.choice` y `Quot.sound`. `lake build` local pasó con Lean 4.35.0, Mathlib v4.35.0 y EllipticPDE `c47acceaf985f59e1cf3257ffea077a73ea99dae`. El CI Lean 4 / Mathlib de la PR #7 pasó en la ejecución [42555075750](https://github.com/MichaelMobius/tesispucp/actions/runs/42555075750).

## Registro de la cuarta etapa

## Cuadrado y condición de Dirichlet exacta

Fuente: Lema 3.19, estimación (3.71), y Teorema 3.20, paso determinista (3.74), de la tesis. La constante óptima `Cₚ = √2/π` se afirma posteriormente en el **Corolario 3.23**, ecuación (3.80); no es una hipótesis del Teorema 3.20.

| Paso | Declaración Lean | Estado y alcance |
|---|---|---|
| `U=(-1,1)²` abierto y acotado | `cuadrado`, `cuadrado_abierto`, `cuadrado_acotado` | Compilado |
| Factor `ψ=(1-x²)(1-y²)` y anulación cuando alguna coordenada tiene cuadrado 1 | `psiCuadrado`, `psiCuadrado_cero_coord0`, `psiCuadrado_cero_coord1` | Compilado; no sustituye una caracterización de la frontera |
| `ψ q` para `q` suave con soporte compacto **interior** | `psiPorPrueba`, `psiPorPrueba_mem_H01` | Compilado; clase más estrecha que la arquitectura PINN de la tesis |
| Convergencia en `L²` de función y gradiente implica pertenencia a `H01`; y recíprocamente un elemento `H01` admite tal aproximación por pruebas | `mem_H01_de_aproximacion_l2`, `existe_aproximacion_l2_de_H01`, `psiPorPrueba_aproximacion_l2` | Compilado; la quinta etapa construye además el recorte para `q` suave sin soporte compacto |
| Cota energética en el cuadrado para `e∈H01`, `Δe=r∈L²` | `energia_dirichlet_cuadrado` | Compilado, por especialización del Lema 3.19 plano |
| Cota (3.74) para la diferencia de grafos `h-u*` | `estimacion_error_dirichlet_exacto` | Compilado **condicionalmente** a `h-u*∈H01` y a la identidad distribucional del residuo |
| Cota para dos candidatos `ψ q` con `q` de soporte interior | `estimacion_psi_por_pruebas` | Compilado; pertenencia `H01` demostrada, identificación de `r` todavía como hipótesis |

## Puentes pendientes

1. **Arquitectura `ψ q`.** El caso `q` globalmente suave ya está probado en la quinta etapa con recorte y convergencia `L²`. Falta el puente de extensión para `q` definida solo en un entorno del cuadrado cerrado y la instancia explícita de la clase de polinomios usada en los comparadores de Hermite.
2. **Funciones suaves `h,u*` con igual valor en toda la frontera.** Falta demostrar directamente que `h-u*∈H01`, sin postular factorización por `ψ`. Con regularidad `C¹` hasta la frontera, la cota `|h-u*|≤d(x,∂U) sup‖∇(h-u*)‖` permite el mismo recorte. Hay que formalizarla en el cuadrado y establecer la convergencia de ambos componentes. Para funciones meramente `H¹` con igual traza se necesita la caracterización `ker(trace)=H01` en este dominio Lipschitz; no se encontró ese puente para `H1Graph.H01` en la revisión fijada de EllipticPDE/Mathlib.
3. **Residuo concreto.** Probar que `Δ(h-u*)=Δh-f` en distribuciones y que el residuo está en `L²`, a partir de las regularidades del Teorema 3.20. El teorema actual lo recibe como igualdad distribucional explícita.
4. **Constante óptima.** `Poincare.BoxSlice` da en el cuadrado una cota cuadrática no óptima `(2)²/2=2` por dirección. Para `Cₚ=√2/π` se necesita la desigualdad de Wirtinger de Dirichlet con constante `(2/π)²` en cada intervalo `(-1,1)`, aplicar Fubini en las dos direcciones y pasar de pruebas a `H01` por densidad. Equivalentemente, formalizar la primera autofrecuencia `λ₁=π²/2` y la expansión espectral usada en el Corolario 3.23.
5. **Teorema 3.20 completo.** Siguen sin formalizarse las clases de redes con Dirichlet exacto, los comparadores/minimizadores y las hipótesis probabilísticas de muestreo. Una penalización finita de frontera no implica traza nula ni permite aplicar esta cota sin un término de frontera adicional.

## Cadena formal previa del Lema 3.19 en ℝ²

Fuente: Lema 3.19 de la tesis (estimación determinista (3.71)) y Teorema 3.20 (resultado PINN posterior). El código nuevo se limita al caso `Plano := EuclideanSpace ℝ (Fin 2)`.

| Paso | Declaración Lean | Estado |
|---|---|---|
| Error en `H₀¹(Ω)` como cierre de grafos de prueba, con `fnL U` y `gradL U` | `H1Graph.H01` de EllipticPDE | Definición de biblioteca |
| `gradL U` es la derivada distribucional de `fnL U` | `h01_gradiente_distribucional`; `H01_le_W12`; `mem_W12_iff_hasWeakFDerivOn` | Compilado |
| `Δ = ∂₁² + ∂₂²` en distribuciones sobre `Ω` abierto | `laplacianoDistribucional`, `laplacianoDistribucional_eq_suma` | Compilado |
| Una derivada direccional de prueba conserva suavidad, soporte compacto y `tsupport ⊆ Ω` | `derivadaPrueba` | Compilado |
| `Δ fnL U = div gradL U` en `𝓓′(Ω)` | `laplaciano_ofFun_eq_div_grad` | Compilado |
| Signo: `⟨ΔU,φ⟩ = -∫ gradL U · ∇φ` | `laplaciano_eval_suma`, `suma_derivadas_eq_producto`, `laplaciano_eval_producto` | Compilado |
| Integrales globales = productos internos `L²(Ω)` | `inner_gradiente_prueba_eq_integral`, `inner_residuo_prueba_eq_integral` | Compilado |
| `ΔU=r` en `𝓓′(Ω)` implica `HasTestLaplacian U r` | `laplaciano_distribucional_implica_prueba` | Compilado |
| Representante `r ∈ L²` único | `laplaciano_distribucional_l2_unico` | Compilado |
| Identidad de Green con prueba `U` por densidad | `green_por_densidad` | Compilado |
| Poincaré con `Cₚ=√(C+1)>0` | `exists_poincare_constant`; `poincare_H01_of_bounded` | Compilado |
| `‖U‖² = ‖fnL U‖² + ‖gradL U‖²` | `norma_sobolev_cuadratica`; `H1Graph.norm_sq_eq` | Compilado |
| `‖U‖ ≤ Cₚ√(1+Cₚ²)‖r‖` | `energia_sobolev_de_laplaciano_distribucional`, `energia_sobolev_plano_volumen` | Compilado |

El enunciado final usa `Ω : Opens Plano` acotado, `U : H1Graph.H01 volume Ω`, `r : Lp ℝ 2 (volume.restrict Ω)` y la igualdad `laplacianoDistribucional Ω (Distribution.ofFun Ω (fnL U) volume ⊤) = Distribution.ofFun Ω r volume ⊤`. Esta igualdad representa con precisión `Δe = r ∈ L²`. La cota usa el `r` único. No requiere hipótesis adicional de Lipschitz: el resultado es válido para el `H01` definido por cierre en cualquier abierto acotado. La tesis asume un dominio Lipschitz, que satisface estas condiciones.

## Dependencias restantes del Teorema 3.20

- Demostrar que la igualdad de trazas de las funciones PINN concretas implica que su diferencia pertenece al `H01` de EllipticPDE. En el cuadrado, se propone la aproximación directa por pruebas descrita arriba.
- Formalizar las funciones `u*`, `hₘ` y la igualdad de su laplaciano residual en los tipos concretos. La forma abstracta de la cota determinista (3.74) para `h-u*` ya compila con las dos premisas analíticas explícitas.
- Formalizar las hipótesis de muestreo, comparadores, minimizadores, densidad y peso residual del Teorema 3.8 para obtener la convergencia y tasa probabilística de 3.20.
- Extender el nuevo puente a dimensión finita general si se desea fuera de `ℝ²`; la prueba actual usa la base ortonormal de dos elementos.

Otros resultados: Teorema 3.8, Lema 3.24, Teoremas 3.4 y 3.18, Proposiciones 3.15 y 3.25 y Corolario 3.26 siguen pendientes como resultados completos. Sus pasos parciales de `Minimalidad.lean` y `RedCuadratica.lean` permanecen compilados.

