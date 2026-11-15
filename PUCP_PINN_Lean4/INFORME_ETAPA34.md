# Informe de la etapa 34

Base [PR #35](https://github.com/MichaelMobius/tesispucp/pull/35), commit `5fc6be834faffad9121aade7bdd52ce994801514`. Se cotejaron las páginas impresas 116–122 y 127–130 del PDF normativo registrado en el inventario.

## Convergencia de los minimizadores manufacturados

`convergencia_neuronal_manufacturada` conserva el selector boreliano de `perdida_minimizadores326_logaritmica`, sus prefijos, la misma ley uniforme en $U=(-1,1)^2$ y el mismo evento casi seguro. `redManufacturada326_eq` identifica la evaluación de la red cuadrática de L3.24 con $\psi p_a$. La continuidad de `pesoSalida324` transfiere la mensurabilidad de los coeficientes a los pesos de salida. Para $m\ge310$ el mínimo es global sobre la clase polinómica y usa exactamente `pesoLogInterior`. La frontera es homogénea para todo tamaño positivo.

`solucionSobolevManufacturada` y `candidatoSobolev326` construyen ambos grafos por el factor $\psi$ y la regularidad global de sus factores. `trazasManufacturadas_iguales` prueba traza cero en ambos casos. `errorSobolevManufacturado` usa el núcleo de la traza para certificar pertenencia a $H_0^1(U)$. Los dos laplacianos distribucionales tienen representantes clásicos en $L^2(U)$ de Lebesgue restringida. El signo del error es $h-u^*$ y `residuoManufacturado326_ae` identifica su laplaciano con $\Delta h-f$, donde $f=\Delta u^*=-2\pi^2 u^*$.

`norma_residuoManufacturado326` demuestra $\|\Delta e\|_{L^2(U)}=2\sqrt{E(h)}$. La ley uniforme es un cuarto de Lebesgue restringida y la norma residual usa Lebesgue sin normalizar. `estimacion_simultanea_manufacturada` aplica C3.23 y conserva la constante explícita
\[
2\left[\frac{\sqrt2}{\pi}\sqrt{1+\frac2{\pi^2}} + \frac{26404}{100000}\right].
\]
La estimación espectral de P3.22 usa la norma esencial y su representante continuo coincide con el error clásico en la clausura. Por tanto, las dos interpretaciones de la norma supremo coinciden en esta clase.

La tasa de pérdida $O(\sqrt{\log(m)/m})$ se transfiere a la suma de errores $H^1+L^\infty$ con tasa $O((\log(m)/m)^{1/4})$, y ambos errores tienden a cero casi seguramente. Este es el régimen logarítmico del párrafo que sigue a (3.94). La familia de mínimos con el peso raíz de (3.94) corresponde a otro funcional. La presente declaración expresa la instancia escalar manufacturada con Dirichlet exacto. Las condiciones de interpolación y regularidad que aparecen como premisas en el resultado abstracto de Shin se obtienen aquí de la construcción de Hermite y C3.26. La cota simultánea espectral y el peso logarítmico corresponden a la tesis. [Shin, Darbon y Karniadakis, Assumption 3.2 y Theorems 3.2–3.4](https://arxiv.org/pdf/2004.01806)

## Proposición 3.27

| Resultado | Declaración Lean | Alcance |
|---|---|---|
| Coeficientes y truncamiento | `taylorManufacturada_coef`, `coefTaylorManufacturada_complejo`, `taylorManufacturada_grado` | Coeficientes de la forma $a^{(k)}(0)/k!$ y grado a lo sumo $N$. |
| (3.92) | `resto_taylorManufacturada_c3` | Cota uniforme $C(N+1)^3 2^{-N}$ en cada derivada de orden a lo sumo tres, para todo $N$ natural. |
| Producto tensorial | `tensorTaylor_error_c3`, `tensorTaylor_grados_parciales`, `tensorTaylor_en_clase` | Cota de todas las derivadas mixtas de orden total a lo sumo tres, grado parcial a lo sumo $N$ y pertenencia a la clase si $N$ respeta el presupuesto de grado. |
| (3.93), grado y salida neuronal | `gradoTaylor327_admisible`, `comparadorTaylor327_red`, `comparadorTaylor327_error_c3` | $N_m=\lceil2\log_2 m\rceil\le4m-1$ para $m\ge1$, con $N_1=0$. Cota $C(1+\log m)^3/m^2$. |
| Residuo y tolerancias | `comparadorTaylor327_cotas_Poisson`, `perdidaEmpiricaTaylor327_cota`, `comparadorTaylor327_criterio_fuerte` y `comparadorTaylor327_tolerancia_empirica` | Control del laplaciano y de la seminorma Hölder. Pérdida empírica uniforme de orden $(1+\log m)^6/m^4$. Criterio fuerte (3.56) y pérdida empírica $O(a_m)$ con ambos pesos. |

La serie de Taylor compleja es la de Mathlib para la función entera ya construida. Cauchy sobre el círculo de radio dos da $\lvert a_j\rvert\le M_2 2^{-j}$. La cola geométrica controla valores en discos de radio $1/(N+2)$ centrados en el intervalo. En estos discos, el factor $(1+1/(N+2))^{N+1}$ está acotado por $e$. Una segunda cota de Cauchy introduce $k!(N+2)^k$, a lo sumo un múltiplo de $(N+1)^3$ para $k\le3$. Esto evita tener que diferenciar cada término de la serie y da la misma tasa que (3.92).

El paso tensorial usa Leibniz para cada factor $(1-t^2)T_N(t)$ y la diferencia de productos para las derivadas mixtas. El máximo de las cotas de parciales representa la convención de máximo de las normas $C^k$. Para una convención con suma basta una constante multiplicativa finita. Las cotas de cada parcial y seminorma Hölder de orden hasta dos se enuncian en la clausura.

`proposicion327` integra la clase, Dirichlet, la tasa $C^3$ y las tolerancias para $m\ge3$, donde se reutiliza la expresión de `pesoLogInterior_eq`. Los lemas de grado y tasa ya valen para $m\ge1$. Para las tolerancias se comparan ambos pesos con $c/m$ y se usa $(1+\log m)^3/m^2\le216/m$ como mayorante auxiliar. La conclusión fuerte es $A\sqrt{a_m}$ y el residuo cuadrático empírico queda a lo sumo $K a_m$, con constantes uniformes. Estas son las premisas de comparación de C3.12 y P3.10 en la instancia interior de Poisson con $\alpha=1/2$. Si un mínimo aproximado tiene tolerancia $\delta_m\le K_\delta a_m$, la suma de tolerancias se acota por $(K+K_\delta)a_m$. Taylor controla el defecto empírico sin imponer interpolación exacta. La versión de C3.12 para operadores arbitrarios queda como obligación separada.

## Resultados específicos de Hermite

`factorHermite325_resto_c3_base_dos_tercios` verifica (3.90) con $N=4r$ para cada proyección. Se aplica (3.89) en el disco de radio $1+1/(N+2)$. El cociente nodal es a lo sumo $\bigl[(2/3)(1+1/(2(N+2)))\bigr]^N$. La potencia del segundo factor está acotada por $e$. Cauchy en la circunferencia centrada en el punto real aporta $(N+1)^3$. Así, la base $2/3$ procede del cociente en un disco que depende de $N$.

`comparador325_horner` construye las capas afines con activación cuadrática y demuestra su evaluación exacta. Ambos Horner se ejecutan en paralelo, completando con ceros los coeficientes de la proyección de menor grado. Cuatro registros requieren ocho neuronas por capa. Hay una capa inicial, $2(4\max(r_x,r_y)-1)$ capas de Horner y cinco capas finales para los factores de frontera y el producto. El recuento verificado es exactamente $8\max(r_x,r_y)+4$ capas ocultas. Esta red depende del comparador y es la realización particular de la página 117. La arquitectura común de L3.24 conserva su propio recuento y la selección boreliana ya formalizada.

## Verificación

Se conservaron Lean 4.35.0, Mathlib v4.35.0 y EllipticPDE `c47acceaf985f59e1cf3257ffea077a73ea99dae`. `lake build` completó 3930 trabajos. Los controles `#check` y `#print axioms` verificaron las declaraciones indicadas. Sus dependencias axiomáticas son `propext`, `Classical.choice` y `Quot.sound`. El SHA-256 del PDF sigue coincidiendo con el inventario.

