# Etapa 36 · interpolación Hölder–L² y muestreo en la frontera

Base [PR #37](https://github.com/MichaelMobius/tesispucp/pull/37), commit `d6d84bfe06d8bf55109af3b5a86452d3168bc8f9`. Se cotejaron L3.9 y (3.34) en las pp. impresas 70–71, y H3.2 y el ejemplo geométrico en las pp. 43–47 del PDF normativo.

## Lema 3.9 y ecuación (3.34)

`lema39_global` trabaja en un espacio pseudométrico con abiertos medibles, medida finita y soporte medible $U$. Supone $H\ge0$, $\alpha,s,\kappa,R>0$, la cota de masa de las bolas abiertas hasta radio $R$, el control Hölder $H$ en $U$ y la integrabilidad de $v^2$. Su conclusión utiliza el supremo puntual en $U$, que también controla la norma esencial para una medida concentrada en $U$. En `lema39_global_acotado`, la acotación de $v$, la concentración y la continuidad Hölder dan la integrabilidad. Esta variante recupera las hipótesis del lema impreso para una probabilidad, con una función en el ambiente que representa la función sobre $U$.

Para $Q=(\int v^2\,d\mu)^{1/2}$ y $p=2\alpha/(2\alpha+s)$, una constante válida es

\[
C=H+\frac{1}{\sqrt\kappa}+\frac{1}{\sqrt{\kappa R^s}}.
\]

La cota es $\sup_U |v|\le C(Q+Q^p)$. Si $Q=0$, el argumento local con energía cero da $|v(x)|\le H r^\alpha$ para todo centro de $U$ y todo radio positivo suficientemente pequeño. `lema39_eq_zero` hace tender esos radios a cero y obtiene anulación puntual. Si $Q>0$ y $Q^{2/(2\alpha+s)}\le R$, la elección del radio convierte ambos términos de la cota truncada en múltiplos de $Q^p$. Si $R<Q^{2/(2\alpha+s)}$, la parte Hölder queda acotada por $H Q^p$ y la parte de energía es $Q/\sqrt{\kappa R^s}$. La igualdad de radios corresponde al primer caso.

`lema39_tasa` aplica esta misma cota a una sucesión con seminormas controladas uniformemente, tamaños $m(n)\to\infty$ y energía $O(m(n)^{-\beta})$ para $\beta>0$. La tasa suprema es $O(m(n)^{-\alpha\beta/(2\alpha+s)})$. Para $\beta=\alpha/2$, las especializaciones $s=2$ y $s=1$ dan los exponentes $\alpha^2/[2(2\alpha+2)]$ y $\alpha^2/[2(2\alpha+1)]$ de (3.28). Las demostraciones previas de T3.8 conservan su dependencia original.

## H3.2 en el cuadrado

`medidaUniformeFrontera` es $\tfrac18\mathcal H^1\!\restriction_{\partial U}$ en el plano euclidiano. `puntoCara_isometria` identifica la longitud en cada cara con Lebesgue unidimensional. Las cuatro caras cerradas cubren la frontera y sus intersecciones tienen longitud cero. `medidaUniformeFrontera_apply` demuestra la fórmula de suma de los cuatro transportes de Lebesgue restringida a $[-1,1]$. La longitud total es ocho, cada cara recibe probabilidad $1/4$, los puntos individuales tienen medida cero y la probabilidad está concentrada en la frontera. `medidaUniformeFrontera_densidad` identifica la densidad constante $1/8$ respecto de Hausdorff restringida.

Para una bola cerrada de radio $r$, la proyección sobre la coordenada libre de cada cara tiene longitud a lo sumo $2r$. La suma normalizada da $\mu_b(\overline B(x,r)\cap\partial U)\le r$. Para $x\in\partial U$ y $0<r\le1$, un segmento de una cara que contiene $x$ en su clausura aporta longitud $r$ dentro de la bola abierta. La masa local es por tanto al menos $r/8$, incluso cuando $x$ es vértice.

`particiones_uniformes_frontera_cuadrado` usa $N=\lceil 2/\eta\rceil$, $\ell=2/N$ y $2\eta/3\le\ell\le\eta$ para $0<\eta\le1$. Dos caras conservan sus extremos y las otras dos los excluyen. Cada cara se subdivide en intervalos semiabiertos con el extremo final asignado una vez. Las celdas son medibles y disjuntas y cubren la frontera. Cada celda contiene un intervalo abierto de longitud $\ell$ en su cara, por lo que su masa es al menos $\ell/8\ge\eta/12$. Su diámetro es a lo sumo $\eta\le\sqrt2\eta$. Esto certifica $c_b=1/12$, $C_b=1$ y $\varepsilon_0=1$ en `datosMasa38_frontera_cuadrado`. La mitad interior ya tiene $c_r=1/9$, $C_r=\pi/4$ y densidad $1/4$ para ese mismo umbral.

`probabilidadMuestrasCuadrado` es el producto de los espacios de sucesiones con sus leyes infinitas correspondientes. `muestreoInteriorCuadrado` y `muestreoFronteraCuadrado` son registros `Muestreo38` en ese mismo espacio y certifican marginales e independencia interna. `muestreosCuadrado_independientes` prueba independencia de las dos sucesiones completas. `muestreosCuadrado_en_soportes` da en un único evento casi seguro la pertenencia de todos los puntos a sus soportes. Los registros de masa y muestreo se pueden aplicar directamente a T3.4 y T3.8. La condición de dominio Lipschitz se mantiene fuera de esta interfaz de masa. Las clases, comparadores y mínimos de H3.7 siguen siendo premisas para una aplicación de dos muestras.

## Generalizaciones de cobertura

- `masa_bola_inferior_dimensional` obtiene L3.3 a partir de particiones con diámetro $D\eta$ y masa $c\eta^s$. Da la constante $c(2D)^{-s}$ hasta radio $2D\varepsilon_0$. Basta especializar $D=\sqrt d$ y los dos exponentes $d,d-1$ para recuperar las dos cotas.
- `lema36_cobertura_dimensional` combina recuento, cota binomial, cota exponencial y cobertura en un evento medible. Acepta celdas con solapamientos de medida cero y factor de diámetro $D$. La noción geométrica de cobertura sobre el soporte no se usa como definición del evento.
- `perdidaPoblacional_le_sumas_dimensional` aplica la desigualdad integral de L3.5 a ambos términos con exponentes independientes $s_r,s_b$. La conclusión conserva ambos pesos residuales y los términos Hölder de operadores y datos. Requiere concentración, cobertura e integrabilidad, igual que la desigualdad determinista anterior.

T3.4 y T3.8 integrados conservan las formulaciones escalares 2D. Quedan la integración del evento de ambos prefijos con los pesos y la aritmética muestral dependientes de $d$, y la rama $d=1$ con su ley de frontera de dimensión cero. Los resultados manufacturados de las etapas 34 y 35 permanecen en la compilación.

## Obligaciones del capítulo

El [inventario auditado](INVENTARIO_FORMAL_CAPITULO_III.md) conserva los 27 rótulos con sus declaraciones y estados. Además de la integración dimensional, quedan la traducción multiíndice literal de L3.1, el T3.20 para dominios Lipschitz generales y la existencia clásica utilizada por T3.18. En la revisión fijada, `EllipticPdes.Regularity.exists_weakSolution_interior_classical` ofrece regularidad en el interior de compactos con ecuación casi en todas partes. Supone transporte nulo, coeficientes con regularidad débil de todos los órdenes y un dato con derivadas débiles de todos los órdenes en $L^2$. La conclusión parte de $H_0^1$ y no incluye continuidad hasta la frontera ni el dato Dirichlet general de H3.16.

## Verificación

Lean 4.35.0, Mathlib v4.35.0 y EllipticPDE `c47acceaf985f59e1cf3257ffea077a73ea99dae`. El PDF normativo conserva SHA-256 `c6c612f7141c8c6ab5730fc0853b6d16222b97e5615e306f2e32191a49b686e0`.

`lake build` completó 4024 trabajos. `#check` y `#print axioms` verificaron los nuevos enunciados. Las declaraciones principales solo dependen de `propext`, `Classical.choice` y `Quot.sound`.
