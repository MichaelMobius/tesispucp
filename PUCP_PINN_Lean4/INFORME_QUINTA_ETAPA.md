# Quinta etapa: recorte interior y Dirichlet exacto en el cuadrado

## Alcance matemático

Dominio: `U=(-1,1)²`. Factor de frontera: `ψ(x,y)=(1-x²)(1-y²)`.
Hipótesis nueva y explícita del resultado principal: `q : Plano → ℝ` es globalmente `C∞` (`ContDiff ℝ ⊤ q`). No se le exige soporte compacto. Esta hipótesis cubre las funciones polinómicas como clase matemática, aunque la instancia Lean de un polinomio bivariado concreto aún no está conectada al teorema. La extensión de una `q` definida solamente en un entorno del cuadrado cerrado tampoco está formalizada.

## Resultados compilados

1. `recorte` es el producto de cuatro perfiles `Real.smoothTransition`; su soporte es compacto y está contenido en el cuadrado. El recorte vale uno en el cuadrado interior a distancia `2δ` de cada cara.
2. `abs_fderiv_recorte_le_norm` prueba `|Dχδ(x)w|≤(4C/δ)‖w‖` para una cota global `C` de la derivada de la transición. `volumen_real_franja` prueba que la franja tiene área `16δ-16δ²` si `0<δ<1/2`; `volumen_real_franja_le` da `≤16δ`.
3. `psiCuadrado_le_en_franja` da `0≤ψ≤4δ` en la franja. `norm_psi_smul_fderiv_recorte_le` deduce `‖ψ Dχδ‖≤16C`, y `norm_fderiv_recortePsi_le` da una cota del gradiente de `χδψq` independiente de `δ`.
4. `recortePsi_tendsto_fnL` y `recortePsi_tendsto_gradL` prueban convergencia en `L²(U)` de valores y gradientes. Se usa convergencia puntual eventual, cotas uniformes e integrabilidad uniforme en el cuadrado de medida finita. La fórmula de área sirve para verificar la geometría, pero la prueba `L²` no necesita su constante numérica.
5. `psiGraph_fnL_ae` y `psiGraph_gradL_ae` identifican los representantes de las dos componentes del grafo. `psiGraph_mem_H01` prueba `ψq∈H1Graph.H01` para `q` globalmente suave, sin factor de soporte compacto.
6. `estimacion_psi_suave_dirichlet_exacto` aplica `estimacion_error_dirichlet_exacto` a la diferencia de dos candidatos `ψqh` y `ψqu`. La pertenencia del error a `H01` ya está demostrada por linealidad.

## Hipótesis conservada en la estimación

`estimacion_psi_suave_dirichlet_exacto` recibe explícitamente `r∈L²(U)` y la igualdad distribucional

`laplacianoDistribucional U (Distribution.ofFun U (fnL (psiGraph qh − psiGraph qu)) volume ⊤) = Distribution.ofFun U r volume ⊤`.

No se ha sustituido esta identidad por un axioma. La identificación de `r` con el residuo concreto de la PINN y la ecuación de `u*` todavía requiere teoremas adicionales.

## Extensiones pendientes

- Funciones `C∞` con igual valor en toda la frontera, sin forma `ψq`: demostrar el control lineal de la función por distancia a la frontera y repetir el recorte en las cuatro caras.
- Funciones `C¹` con traza cero: puede requerirse mollificación después del recorte para obtener pruebas `C∞`, además del control de gradientes.
- Funciones `H¹` generales: formalizar un operador traza en el cuadrado y probar `ker(trace)=H1Graph.H01`.
- Comparadores de Hermite: conectar su representación polinómica Lean concreta con `ContDiff` y con `psiGraph`.
- Constante óptima `Cₚ=√2/π`: probar Poincaré óptima mediante Wirtinger en cada sección y densidad, o la primera autofrecuencia del cuadrado.
- Teorema 3.20 completo: quedan por formalizar la clase de PINN, la identificación del residuo, las condiciones de muestreo, las trazas generales y la convergencia probabilística. Una penalización finita de frontera no equivale al caso Dirichlet exacto aquí probado.

## Verificación local

- `lake build`: éxito (3187 trabajos).
- `#print axioms`: para los teoremas nuevos, únicamente `propext`, `Classical.choice`, `Quot.sound`.
- Búsqueda de `sorry`, `admit`, `axiom` en los módulos nuevos: ninguna ocurrencia.
- Lean `v4.35.0`, Mathlib `v4.35.0`, EllipticPDE `c47acceaf985f59e1cf3257ffea077a73ea99dae`.
- No se modificaron las pruebas previas ni el PDF de la tesis.
- CI de la PR de quinta etapa: pendiente de ejecución remota al abrirla.
