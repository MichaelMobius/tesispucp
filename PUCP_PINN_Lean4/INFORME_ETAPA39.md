# Etapa 39 · Energía de Poisson en dimensión finita

Base [PR #40](https://github.com/MichaelMobius/tesispucp/pull/40), commit `f32acd06d334b1c7618dd035a7d813f61e88cbc1`. El cotejo usa las páginas impresas 98–103 del PDF normativo. Se usó el auxiliar LaTeX para confirmar las barras de clausura de $C^0(\overline U)$.

## Lema 3.19

El enunciado impreso toma un dominio Lipschitz acotado en $\mathbb R^d$, una constante de Poincaré $C_P>0$, $e\in H_0^1(U)$ y $\Delta e\in L^2(U)$. La conclusión (3.71) usa la norma completa $H^1$. La acotación basta para la existencia de la constante cuando la condición de borde se expresa mediante el cierre de funciones de prueba.

`HasDistributionalLaplacianDimensional` expresa la igualdad en $\mathcal D'(U)$ entre el laplaciano de `fnL` y la distribución del representante `r : Lp ℝ 2`. `laplacianoDistribucionalDimensional` usa `LineDeriv.laplacianCLM`. En una base ortonormal finita, el operador suma las segundas derivadas direccionales. La caracterización de `W12` identifica la primera derivada con la componente del gradiente débil. Integrar la segunda derivada contra una prueba compactamente soportada aporta el signo menos, con

$$
\langle\Delta e,\varphi\rangle=-\int_U\nabla e\cdot\nabla\varphi.
$$

`laplaciano_dimensional_implica_prueba` pasa de esa evaluación al producto de $L^2$, con el mismo `r` a ambos lados del puente. `laplaciano_dimensional_l2_unico` garantiza su unicidad como clase. La inclusión `H01_le_W12` y `green_por_densidad` permiten tomar al propio error como prueba. `H1Graph` usa la norma hilbertiana del par formado por la función y su gradiente débil. Los argumentos algebraicos se reutilizan de `energia_norma_par_debil`.

`lema319_constante_dada` conserva cualquier $C_P$ admisible. `lema319_cuadrado_constante_optima` lo aplica con $C_P=\sqrt{2}/\pi$ mediante `poincare_cuadrado_espectral`. `lema319_dimensional` produce una constante positiva uniforme para todos los errores y residuos de un abierto acotado. Se aplica a Lebesgue en $\mathbb R^d$ para $d\ge1$. La declaración general también admite cualquier medida de Haar aditiva en un espacio real euclídeo de dimensión finita positiva.

## Teorema 3.20

La tesis toma $L=\Delta$, $\Gamma=\partial U$, $u^*\in H^1(U)\cap C^0(\overline U)$ con $\Delta u^*=f\in L^2(U)$, y candidatos de la misma traza con laplaciano en $L^2$. Las clases afines deben seguir satisfaciendo H3.7, incluidos comparadores exactos de regularidad uniforme y una selección mensurable de mínimos globales. La demostración usa $u^*-h$ y $f-\Delta h$. `laplaciano_dimensional_resta` usa $h-u^*$ y $\Delta h-f$, con la misma norma, mediante la linealidad de `fnL`, `Distribution.ofFun` y el laplaciano.

| Ecuación | Declaración | Alcance |
|---|---|---|
| (3.74) | `estimacion320_dimensional` | Cota para cualquier par Sobolev con error en $H_0^1$ y los dos laplacianos en $L^2$. |
| (1.3) y (3.73) | `cota_L2_cambio_medida`, `estimacion320_de_perdida` | Para $\mu_r=\rho\,dx$, $\rho\ge\rho_0>0$ casi en todas partes y $\lambda_r>0$, la constante de la cota por la raíz de pérdida es $C_P\sqrt{1+C_P^2}/\sqrt{\rho_0\lambda_r}$. |
| (3.72) y (3.75) | `cota_L2_de_supremo_puntual`, `estimacion320_de_supremo` | El residuo en $L^2$ se acota por el supremo puntual de un representante acotado, multiplicado por la raíz del volumen. Para la versión esencial se usa `cota_L2_de_supremo_esencial`. |
| (3.72)–(3.75) | `teorema320_dimension_ge_dos` | Invoca T3.8 con los mismos prefijos $m_r(n),m_b(n)$, clases y selecciones. Da convergencia $H^1$ y ambos órdenes casi seguramente, $m_r^{-\alpha/(2d)}$ y $m_r^{-\alpha^2/[d(2\alpha+d)]}$. Para $d=2$, el primero es $m_r^{-\alpha/4}$. |
| Rama con extremos deterministas | `teorema320_unidimensional` | En $(a,b)$ usa T3.8 unidimensional. Da convergencia y tasas $m_r^{-\alpha/2}$ por pérdida y $m_r^{-\alpha^2/(2\alpha+1)}$ por supremo. |

La medida de Lebesgue se restringe a $U$ antes de aplicar `withDensity`; la ley así formada se exige de probabilidad en el teorema estadístico. La igualdad casi en todas partes entre el residuo de la pérdida y el de la energía se deriva restando las dos identificaciones `hRep` y `hf`. La finitud del término ponderado se obtiene del control Hölder en el soporte acotado con medida de probabilidad. El término de frontera es no negativo y la pérdida domina el término residual. El argumento funciona con cota inferior de densidad.

La prueba de (3.72) usa el límite del supremo interior de T3.8. El paso a (3.75) usa una desigualdad entre el supremo puntual y $L^2$; `supResiduo_eq_Linfty` permite identificarlos como supremo puntual y esencial cuando hay continuidad relativa en el abierto y la medida da masa positiva a los abiertos no vacíos. La versión por cota esencial se enuncia para un supremo esencial finito.

## Alcance de la traza y de las selecciones

El teorema integrado recibe un grafo `W12` para cada candidato, la ecuación distribucional y la identificación puntual del residuo en la medida de volumen. El operador de frontera pertenece a la interfaz de T3.8. La aplicación a Dirichlet clásico requiere identificar esa evaluación y el dato $g$ con las trazas de los grafos. El resultado energético usa la condición afín `hDiri` expresada en $H_0^1$.

`diferencia_mem_H01_de_traza` deduce esa condición de la igualdad de imágenes bajo un operador lineal continuo sobre `W12` cuyo núcleo se haya caracterizado. `estimacion320_de_trazas_iguales` aplica (3.74) bajo esa premisa. Para el cuadrado existen `trazaSobolevCuadrado`, `nucleo_trazaSobolevCuadrado_eq_H01` y `trazaSobolevCuadrado_continua`. En las revisiones fijadas de Mathlib y EllipticPDE no se encontró una construcción general de $\operatorname{Tr}:H^1(U)\to H^{1/2}(\partial U)$ con el núcleo requerido. Para recuperar la formulación literal de T3.20 en un dominio Lipschitz general quedan la construcción o importación de esa traza para los grafos, la identificación con la restricción de los representantes continuos y el teorema del núcleo.

Las hipótesis estadísticas siguen siendo las de la interfaz escalar de T3.8 en régimen raíz, con el crecimiento eventual de ambos prefijos, la comparación de tamaños, las particiones y la masa de bolas de H3.2. Las selecciones mensurables y las propiedades de los mínimos y comparadores se reciben como en H3.7. El límite se expresa mediante `∀ᵐ`. La mensurabilidad del candidato como elemento de su clase no establece por sí sola la mensurabilidad del mapa hacia `H1Graph`; para identificar el evento exacto de convergencia como medible se puede suministrar la mensurabilidad de esa realización Sobolev.

## Teorema 3.18 con solución clásica dada

`teorema318_dimension_ge_dos` obtiene (3.69)–(3.70) para todo $d\ge 2$. Los operadores de T3.8 son la evaluación de $L$ y la evaluación en la frontera, con las seminormas Hölder de ambos. Se usa la cota `cota318_error_dirichlet` en la clausura y se comparan los exponentes de los dos residuos para obtener $O(m_r^{-\alpha^2/[d(2\alpha+d)]})$. La existencia de la solución clásica bajo las hipótesis de Gilbarg–Trudinger sigue siendo una obligación independiente.

## Verificación

`lake build` completó 4034 trabajos con Lean 4.35.0, Mathlib v4.35.0 y EllipticPDE `c47acceaf985f59e1cf3257ffea077a73ea99dae`. Los `#check` y `#print axioms` de las declaraciones principales se ejecutan durante la compilación. Las pruebas nuevas dependen únicamente de `propext`, `Classical.choice` y `Quot.sound`. El SHA-256 del PDF normativo coincide con el registrado en el inventario, `c6c612f7141c8c6ab5730fc0853b6d16222b97e5615e306f2e32191a49b686e0`.
