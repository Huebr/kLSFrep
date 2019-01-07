#include <iostream>                  // for std::cout
#include <utility>                   // for std::pair
#include <algorithm>                 // for std::for_each
#include <boost/graph/graph_traits.hpp> // for creation of descriptors vertex and edges.
#include <boost/graph/adjacency_list.hpp> //for usage of adjacency list]
#include <boost/graph/filtered_graph.hpp>
#include <boost/graph/connected_components.hpp>
#include <ilcplex/ilocplex.h>
#include <boost/dynamic_bitset.hpp>
#include <unordered_set>
ILOSTLBEGIN //initialization make vs work properly

using namespace boost;
typedef adjacency_list<vecS, vecS, undirectedS, no_property, property<edge_color_t, int>> graph_t;
//peharps later remove supersource
typedef dynamic_bitset<> db;

//template function to print edges.
template<class EdgeIter, class Graph>
void print_edges(EdgeIter first, EdgeIter last, const Graph& G) {
	typedef typename property_map<Graph, edge_color_t>::const_type ColorMap;
	ColorMap colors = get(edge_color, G);
	//make color type generic
	//typedef typename property_traits<ColorMap>::value_type ColorType;
	//ColorType edge_color;
	for (auto it = first; it != last; ++it) {
		std::cout << "Edge: " << "(" << source(*it, G) << "," << target(*it, G) << ") " << " Color: " << colors[*it] << "\n";
		std::cout << "Edge: " << "(" << target(*it, G) << "," << source(*it, G) << ") " << " Color: " << colors[*it] << "\n";
	}
	cout << " Number of vertex: " << num_vertices(G) << std::endl;
	cout << " Number of edges: " << num_edges(G) << std::endl;
}

template <typename EdgeColorMap, typename ValidColorsMap>
struct valid_edge_color {
	valid_edge_color() { }
	valid_edge_color(EdgeColorMap color, ValidColorsMap v_colors) : m_color(color), v_map(v_colors) { }
	template <typename Edge>
	bool operator()(const Edge& e) const {
		return v_map.test(get(m_color, e));
	}
	EdgeColorMap m_color;
	ValidColorsMap v_map;
};

template<class Graph, class Mask>
void print_filtered_graph(Graph &g, Mask valid) { //pay atention to the position of the bits and the colors positions in array
	typedef typename property_map<Graph, edge_color_t>::type EdgeColorMap;
	typedef typename boost::dynamic_bitset<> db;
	typedef filtered_graph<Graph, valid_edge_color<EdgeColorMap, db> > fg;

	valid_edge_color<EdgeColorMap, Mask> filter(get(edge_color, g), valid);
	fg tg(g, filter);
	print_edges(edges(tg).first, edges(tg).second, tg);
}
template<class Graph, class Mask>
int get_components(Graph &g, Mask &m, vector<int> &components) {
	typedef typename property_map<Graph, edge_color_t>::type EdgeColorMap;
	typedef typename boost::dynamic_bitset<> db;
	typedef filtered_graph<Graph, valid_edge_color<EdgeColorMap, db> > fg;

	valid_edge_color<EdgeColorMap, Mask> filter(get(edge_color, g), m);
	fg tg(g, filter);
	int num = connected_components(tg, &components[0]);
	return num;
}

template<class Graph>
property_map<graph_t, edge_color_t>::type get_colors(Graph &g) {
	typedef typename property_map<Graph, edge_color_t>::type ColorMap;
	ColorMap colors = get(edge_color, g);
	//make color type generic
	return colors;
}


//Callbacks new to me new to you let god save my soul

//basic definitions
typedef IloArray<IloBoolVarArray> IloVarMatrix;

//cuts 
ILOLAZYCONSTRAINTCALLBACK4(MyLazyCall,IloBoolVarArray,Z,IloBoolVarArray,Y, IloVarMatrix,X ,graph_t,g ) {
	int size = Z.getSize();
	int n_vertices = Y.getSize();
	db temp(size);
	int n_comp_sol = 0;
	std::vector<int> components(num_vertices(g));
	auto colors = get_colors(g);
	graph_traits<graph_t>::edge_iterator it, end;
	for (int j = 1; j < n_vertices; ++j) { //using colors of original graph
		if (getValue(Y[j])==1) n_comp_sol+=1;
	}
	for (int i = 0; i < size; ++i) { //using colors of original graph
		if (getValue(Z[i])==1) temp.set(i);
	}
	std::cout << " user cutting" << std::endl;
	int num_c = get_components(g, temp, components) - 1;//vertex 0 isolated
	if (num_c !=n_comp_sol) {
		std::cout << "add user cut" << std::endl;
		for (volatile int u = 1; u < n_vertices; ++u) {
			if (getValue(Y[u]) == 1) {
				for (volatile int v = u + 1; v < n_vertices; ++v) {
					if (getValue(X[u][v]) == 1) {
						db temp1(size);
						IloExpr expr(getEnv());
						if (components[u] != components[v]) {
							std::tie(it, end) = edges(g);
							while (it != end) {
								if (components[source(*it, g)] != components[target(*it, g)]) {
									if (components[source(*it, g)] == components[u] || components[target(*it, g)] == components[u]) {
										temp1.set(colors[*it]);
									}
								}
								++it;
							}
							for (int i = 0; i < Z.getSize(); ++i) if (temp1.test(i))expr += Z[i];
							add(expr >= X[u][v]).end();
							expr.end();
						}
							
					}
				}
			}
		}
	}
	else std::cout << "is good" << std::endl;
}


template<class Graph>
void buildRepModel(IloModel mod, IloBoolVarArray Y, IloBoolVarArray Z, IloVarMatrix X, const int k, const Graph &g) {
	IloEnv env = mod.getEnv();
	int n_colors = Z.getSize();
	typedef typename property_map<Graph, edge_color_t>::const_type ColorMap;
	ColorMap colors = get(edge_color, g);
	//modelling objective function
	IloExpr exp(env);
	int n_vertices = num_vertices(g);
	for (int i = 1; i < n_vertices; ++i) {
		exp += Y[i];
		Y[i].setName(("y" + std::to_string(i)).c_str());
	}
	Y[0].setName("y0");
	mod.add(IloMinimize(env, exp));
	exp.end();

	for (int i = 0; i < n_vertices; ++i) {
		X[i] = IloBoolVarArray(env, n_vertices);
	}
	//setting up names to x
	for (int i = 0; i < n_vertices; ++i) {
		for (int j = 0; j < n_vertices; ++j) {
			X[i][j].setName(("x_" + std::to_string(i) + "_" + std::to_string(j)).c_str());
		}
	}
	//setting names to labels variables.
	for (int i = 0; i<n_colors; ++i) {
		Z[i].setName(("z" + std::to_string(i)).c_str());
	}


	//first constraint 
	for (int u = 1; u < n_vertices; ++u) {
		for (int v = u + 1; v<n_vertices; ++v) mod.add(X[u][v]<=Y[u]);
	}
	//second constraint
	IloExpr e2(env);
	for (int u = 1; u < n_vertices; ++u) {
		for (int v = u + 1; v<n_vertices; ++v) e2 += X[u][v];
	}
	for (int u = 1; u < n_vertices; ++u) e2 += Y[u];
	mod.add(e2 == n_vertices);
	e2.end();

	//third constraint
	//relaxed add as cuts

	// new temporary constraints 

	//constraint try to strength forest
	IloExpr exptreecut(env);
	typedef typename graph_traits<Graph>::edge_iterator eit;
	eit it, end;
	std::tie(it, end) = edges(g);
	while (it != end) {
		exptreecut += Z[colors[*it]];
		++it;
	}
	int N = num_vertices(g) - 1;
	for (int u = 1; u < n_vertices; ++u) exptreecut += Y[u];
	mod.add(exptreecut >= N);
	exptreecut.end();

	/*new constraint prohibition of usage of edges of diferent components(representatives) not completed
	IloExpr expdcomp(env);
	std::tie(it, end) = edges(g);
	while (it != end) {
		int u, v;
		u = source(*it, g);
		v = target(*it, g);
		if (u > v) std::swap(u, v);
		expdcomp += Z[colors[*it]] - Y[u] - Y[v];
		for (int i = 1; i < u; ++i) {
			expdcomp -= X[i][u];
		}
		for (int i = u + 1; i < u; ++i) {
			expdcomp -= X[i][u];
		}

		++it;
	}
	expdcomp.end();*/
	//forth constraint
	IloExpr texp(env);
	for (int i = 0; i < n_colors; ++i) {
		texp += Z[i];
	}
	mod.add(texp <= k);
	texp.end();

}




int main()
{
	enum { A, B, C, D, E, F, G, H };
	typedef std::pair<int, int> Edge;
	graph_traits<graph_t>::edge_iterator it, end;
	const int n_vertices = 14;
	const int k = 4;
	Edge edge_array[] = {
		Edge(1,2),  Edge(1,12), Edge(2,3),  Edge(3,4),
		Edge(4,5),  Edge(5,6),  Edge(5,8),  Edge(5,9),
		Edge(5,11), Edge(5,13), Edge(6,7),  Edge(7,8),
		Edge(8,9),  Edge(9,10), Edge(10,11),Edge(11,12),
		Edge(12,13),
	};
	int n_edges = sizeof(edge_array) / sizeof(edge_array[0]);
	const int colors[] = { H,H,D,D,C,F,E,D,C,F,G,E,A,B,G,A,B };

	graph_t g(edge_array, edge_array + n_edges, colors, n_vertices);
	//add edges to super source vertex index 0. remember!!!
	std::unordered_set<int> st(colors, colors + sizeof(colors) / sizeof(colors[0]));
	int n_colors = st.size();
	st.clear();//note use end because it is an iterator
	//for (int i = 1; i < n_vertices; ++i) boost::add_edge(0, i, property<edge_color_t, int>(n_colors + i - 1), g);
	std::tie(it, end) = boost::edges(g);
	print_edges(it, end, g);


	//temporario contar numero de cores
	//n_colors += n_vertices - 1;


	//starting cplex code part
	IloEnv   env; //environment
	try {
		IloModel model(env);
		IloBoolVarArray Y(env, n_vertices), Z(env, n_colors);
		IloVarMatrix    X(env, n_vertices); 
		buildRepModel(model, Y, Z, X, k, g);
		IloCplex cplex(model);
		cplex.exportModel("kSLF_rep.lp"); // good to see if the model is correct
											//cross your fingers
		cplex.use(MyLazyCall(env,Z,Y,X,g));
		cplex.solve();
		cplex.out() << "solution status = " << cplex.getStatus() << endl;

		cplex.out() << endl;
		cplex.out() << "Number of components   = " << cplex.getObjValue() << endl;
		for (int i = 0; i < Z.getSize(); i++) {
			cplex.out() << "  Z" << i << " = " << cplex.getValue(Z[i]) << endl;
		}
		for (int i = 1; i < Y.getSize(); ++i) {
			cplex.out() << "  Y" << i << " = " << cplex.getValue(Y[i]) << endl;
		}

	}
	catch (IloException& e) {
		cerr << "Concert exception caught: " << e << endl;
	}
	catch (...) {
		cerr << "Unknown exception caught" << endl;
	}
	//memory cleaning
	env.end();

	return 0;
}