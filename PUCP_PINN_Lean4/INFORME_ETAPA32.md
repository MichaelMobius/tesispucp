# Informe de la etapa 32

Base [PR #33](https://github.com/MichaelMobius/tesispucp/pull/33), commit `14451ed0184e91ad51cb42d56bd498bcd7a00c55`. Referencia normativa, páginas impresas 116–122, registrada en el inventario.

## Cancelación y ecuación (3.89)

Sea $Q(z)=\prod_j(z-t_j)^4$, con $t_j\in[-1,1]$. Si $p\ne0$ y $\deg p<4n$, el grado de $p$ es a lo sumo $d=4n-1$. En una circunferencia de radio $R\ge8$, la norma de su evaluación se acota por $R^d$ multiplicado por la suma de las normas de sus coeficientes. Cada factor nodal tiene módulo al menos $R/2$ antes de elevarlo a la cuarta potencia. También $|\zeta-z|\ge R/2$ si $|z|<4$. Así, el integrando polinómico está acotado por $K/R^2$, donde $K$ puede depender de $p$ y $z$. La norma de la integral es a lo sumo $2\pi K/R$.

Los posibles polos se encuentran en los nodos y en $z$. El integrando es diferenciable en el anillo entre los radios $4$ y $R$, y continuo en ambos bordes. `restoContornoHermite_polinomio_cero` aplica el teorema de Cauchy de Mathlib en el anillo y usa la cota válida para todo $R\ge8$ para concluir que la integral es cero. `restoContornoHermite_formula` resta las integrales de $a$ y $p$ y recupera la igualdad (3.89) con numerador $a$, orientación positiva, factor $(2\pi i)^{-1}$ y signo $a-p$. El factor constante $Q(z)$ está incorporado en el integrando. `factorHermite325_formula` especializa el resultado al interpolante real prolongado a $\mathbb C$.

## Regularidad uniforme y ecuación (3.90)

La continuidad de la prolongación entera de $a$ y la compacidad de la circunferencia de radio $4$ producen una cota $M_a$. `factorHermite325_resto_uniforme` combina (3.89) con la cota previa del cociente nodal y obtiene en $|z|\le3/2$ el mayorante $C(5/6)^{4n}$, con $C=4M_a/(4-3/2)$. En la circunferencia de radio $1/2$ centrada en $t\in[-1,1]$, `factorHermite325_derivadas_resto_uniforme` aplica la estimación de Cauchy de Mathlib y obtiene $k!\,2^k C(5/6)^{4n}$. `iteratedDeriv_eje_real` identifica estas derivadas con las derivadas iteradas reales. `factorHermite325_c3_uniforme` combina las cotas del resto con cotas fijas para las cuatro derivadas de $a$.

El exponente geométrico obtenido por Cauchy en el disco ampliado es $(5/6)^N$, con $N=4n$. El mayorante específico de (3.90) es del tipo $(1+N)^3(2/3)^N$ y procede de diferenciar los productos en el intervalo real. Esa tasa específica queda pendiente. La estimación por discos demuestra la cota uniforme $C^3$ exigida en (3.88).

## Tensor, solución y seminorma Hölder

`comparador325_c3_uniforme` acota cada derivada mixta de orden total a lo sumo tres del tensor y del comparador obtenido al multiplicarlo por $\psi$. La cota representa la norma que toma el máximo de las derivadas en la clausura. Para la convención con suma basta multiplicarla por diez. Leibniz se aplica a los productos $(1-t^2)p_j(t)$, cuyos derivados se acotan por una suma finita con pesos binomiales. El producto tensorial combina las derivadas parciales en cada coordenada. La cota común es independiente del número de muestras, del número de nodos distintos y de su separación.

`laplaciano_comparador325_holder_uniforme` usa la identidad $P_0''P_1+P_0P_1''$, con $P_j=(1-t^2)p_j$, la desigualdad del valor medio y el control de cada distancia coordenada por la euclidiana. En la clausura se usa $\operatorname{dist}(x,y)\le4$ y, por ello, $\operatorname{dist}(x,y)\le2\sqrt{\operatorname{dist}(x,y)}$. La conclusión acota la seminorma exacta, definida como el ínfimo de las constantes válidas. Este control corresponde a $\alpha=1/2$ y puede restringirse al interior. `datosPoisson325_regulares` verifica la suavidad global de la solución y la regularidad Hölder de la fuente fija en la clausura.

## Selección boreliana

En cada estrato no vacío se fija una muestra de referencia. Para cada nodo ordenado de esa referencia se toma el índice mínimo del conjunto de índices con esa coordenada. El patrón de orden preserva las coincidencias y la separación entre clases. Los mismos índices representan exactamente los nodos distintos de cualquier muestra del estrato.

`matrizHermite325` expresa la aplicación de jets en la base de monomios y enumera las filas por pares de nodo y orden. Cada entrada es la evaluación de la derivada de un monomio en un nodo, y los datos evalúan las derivadas de $a$. La inyectividad de `mapaJetsHermite` implica que el determinante es unidad. La continuidad de la inversa en matrices con determinante no nulo da la continuidad de cada coeficiente en el estrato. La unicidad de Hermite identifica el interpolante resuelto en esas coordenadas con `factorHermite325`. Los estratos son disjuntos y cada muestra pertenece a un estrato. La preimagen de cualquier conjunto boreliano se obtiene como unión finita de las imágenes de las preimágenes por las inclusiones de los estratos medibles. Así se obtienen `coeficientesHermite325_borel` y, por `pesosSalida324_continuos`, `pesosSalidaHermite325_borel`.

## Correspondencia con la proposición impresa

`proposicion325_arquitectura_comun` fija una arquitectura para cada $m\ge1$, antes de cuantificar sobre las muestras. Para todas las muestras en la clausura, incluidas las que tienen coordenadas repetidas, reúne mensurabilidad de pesos de salida, realización del comparador, grados parciales a lo sumo $4m-1$, Dirichlet, interpolación del laplaciano, pérdida empírica cero, cota $C^3$ y seminorma Hölder uniforme. La identidad de pérdida se refiere al término empírico. La constante de regularidad se cuantifica antes de $m$.

La página impresa 117 también enuncia una red particular de ancho a lo sumo ocho y profundidad a lo sumo $8\max(r_x,r_y)+4$. Su verificación por Horner queda pendiente. El teorema integrado corresponde a la arquitectura común de L3.24, con las cotas dimensionales de ese lema. Para C3.26 todavía se requieren coercividad, existencia y selección boreliana de minimizadores en la clase finita dimensional.

## Verificación

Lean `4.35.0`, Mathlib `v4.35.0` y EllipticPDE `c47acceaf985f59e1cf3257ffea077a73ea99dae`. `lake build` completó 3913 trabajos y se inspeccionaron `#check` y `#print axioms`. Las declaraciones nuevas auditadas dependen de `propext`, `Classical.choice` y `Quot.sound`. El PDF normativo conserva su SHA-256.

