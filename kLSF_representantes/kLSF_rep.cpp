#include <iostream>                  // for std::cout
#include <utility>                   // for std::pair
#include <algorithm>                 // for std::for_each
#include <boost/graph/graph_traits.hpp> // for creation of descriptors vertex and edges.
#include <boost/graph/adjacency_list.hpp> //for usage of adjacency list
#include <boost/graph/graphml.hpp>
#include <boost/graph/connected_components.hpp>
#include <ilcplex/ilocplex.h>
#include <boost/dynamic_bitset.hpp>
#include <boost/program_options.hpp>
#include <boost/algorithm/string/split.hpp>
#include <boost/algorithm/string/classification.hpp>
#include <boost/algorithm/string/trim.hpp>
#include <boost/graph/filtered_graph.hpp>
#include <boost/exception/all.hpp>
#include <exception>
#include <vector>
ILOSTLBEGIN //initialization make vs work properly

using namespace boost;
namespace po = boost::program_options;
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
	std::cout << " Number of vertex: " << num_vertices(G) << std::endl;
	std::cout << " Number of edges: " << num_edges(G) << std::endl;
	std::vector<int> components(num_vertices(G));
	int num = connected_components(G, &components[0]);
	std::vector<int>::size_type i;
	std::cout << "Total number of components: " << num << std::endl;
	for (i = 0; i != components.size(); ++i)
		std::cout << "Vertex " << i << " is in component " << components[i] << std::endl;
	std::cout << std::endl;
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
ILOLAZYCONSTRAINTCALLBACK5(MyLazyCall,IloBoolVarArray,Z,IloBoolVarArray,Y, IloVarMatrix,X ,int,k,graph_t&,g ) {
	int size = Z.getSize();
	int n_vertices = Y.getSize();
	db temp(size);
	int n_comp_sol = 0;
	std::vector<int> components(num_vertices(g));
	auto colors = get_colors(g);
	//std::cout << "add lazy cut: " << std::endl;
	volatile float y, z, x;
	graph_traits<graph_t>::edge_iterator it, end;
	for (int i = 0; i < n_vertices; ++i) { //using colors of original graph
		//std::cout << "Y[" << i << "]= " << getValue(Y[i]) << std::endl;
		if (std::abs(getValue(Y[i]) - 1) <= 1e-3) n_comp_sol++;
	}
	//std::cout << "Solution values:";
	for (volatile int j = 0; j < size; ++j) { //using colors of original graph
		//std::cout <<"Z["<<i<<"]= "<< getValue(Z[i]) << std::endl;
		double z = getValue(Z[j]);
		//std::cout <<" "<< z << std::endl;
		if (std::abs(getValue(Z[j])-1) <= 1e-3) {
			//std::cout << "set " << j<<std::endl;
			temp.set(j);
		}
	}
	//std::cout<<std::endl;
	//std::cout << " user cutting" << std::endl;
	int num_c = get_components(g, temp, components);//vertex 0 isolated
	if (num_c != n_comp_sol) {
		//new cut
		IloExpr newexpr(getEnv());
		for (int i = 0; i < n_vertices; ++i) { 
			newexpr += Y[i];
		}
		for (int i = 0; i < Z.getSize(); ++i) {
			if (temp.test(i))newexpr -= num_c*Z[i];
		}
		int tmp = -num_c * k + num_c;
		//std::cout << (newexpr >= tmp) << std::endl;
		add(newexpr>=tmp);
		newexpr.end();

		/*for (int u = 0; u < n_vertices; ++u) {
			if (std::abs(getValue(Y[u]) - 1) <= 1e-3) {
				for (int v = u + 1; v < n_vertices; ++v) {
					//std::cout << "X[" << u <<","<<v<< "]= " << getValue(X[u][v]) << std::endl;
					if (std::abs(getValue(X[u][v]) - 1) <= 1e-3) {
						db temp1(size);
						volatile int s, t;
						IloExpr expr(getEnv());
						IloExpr expr2(getEnv());
						if (components[u] != components[v]) {
							std::tie(it, end) = edges(g);
							while (it != end) {
								s = source(*it, g);
								t = target(*it, g);
								if (components[s] != components[t]) {
									if (components[s] == components[u] || components[t] == components[u]) {
										temp1.set(colors[*it]);
									}
								}
								++it;
							}
							for (int i = 0; i < Z.getSize(); ++i) {
								if (temp.test(i))expr += Z[i];
								//if (temp1.test(i))expr2 += Z[i];
							}
							//new cut peharps faster
							//std::cout << (expr <= k - X[u][v]) << std::endl;
							//std::cout << (expr2 >= X[u][v]) << std::endl;
							add(expr <= k - X[u][v]).end();
							//add(expr2 >= X[u][v]).end();
							expr.end();
							expr2.end();

						}

					}
				}
			}
		}*/
	}
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
	for (int i = 0; i < n_vertices; ++i) {
		exp += Y[i];
		Y[i].setName(("y" + std::to_string(i)).c_str());
	}
	mod.add(IloMinimize(env, exp));
	//mod.add(exp>=2);
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
	for (int u = 0; u < n_vertices; ++u) {
		for (int v = u + 1; v<n_vertices; ++v) mod.add(X[u][v]<=Y[u]);
	}
	//second constraint
	IloExpr e2(env);
	for (int u = 0; u < n_vertices; ++u) {
		for (int v = 0; v<u; ++v) e2 += X[v][u];
		e2 += Y[u];
		mod.add(e2 == 1);
		e2.clear();
	}
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
	int N = num_vertices(g);
	for (int u = 0; u < n_vertices; ++u) exptreecut += Y[u];
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
	mod.add(texp == k);
	texp.end();

}


template<class Graph>
void solveModel(int n_vertices, int n_colors, int k, Graph &g) {
	//starting cplex code part
	IloEnv env; //environment
	try {
		IloModel model(env);
		IloBoolVarArray Y(env, n_vertices), Z(env, n_colors);
		IloVarMatrix    X(env, n_vertices);
		buildRepModel(model, Y, Z, X, k, g);
		IloCplex cplex(model);
		cplex.exportModel("kSLF_rep.lp"); // good to see if the model is correct
										  //cross your fingers
		//cplex.setParam(IloCplex::Param::Preprocessing::Presolve, 0);
		//cplex.setParam(IloCplex::Param::MIP::Display, 5);
		//cplex.setParam(IloCplex::Param::Tune::Display, 3);
		//cplex.setParam(IloCplex::Param::Simplex::Display, 2);
		//cplex.setParam(IloCplex::Param::Preprocessing::Dual, 0);
		//cplex.setParam(IloCplex::PreInd, 0);
		//cplex.use(MyUserCall(env, Z, Y, X, k, g));
		cplex.use(MyLazyCall(env, Z, Y, X,k, g));
		cplex.setParam(IloCplex::Param::Threads, 4);//n threads
		cplex.solve();
		cplex.out() << "solution status = " << cplex.getStatus() << endl;

		cplex.out() << endl;
		cplex.out() << "Number of components   = " << cplex.getObjValue() << endl;
		db temp(n_colors);
		cplex.out() << "color(s) solution:";
		for (int i = 0; i < Z.getSize(); i++) {
			if (cplex.getValue(Z[i])) {
				temp.set(i);
				cplex.out() << " " << i;
			}
		}
		cplex.out() << endl;
		cplex.out() << "root(s) solution:";
		for (int i = 0; i < Y.getSize(); i++) {
			if (cplex.getValue(Y[i])) {
				cplex.out() << " " << i;
				/*for (int j = i + 1; j < n_vertices; j++) {
					cplex.out() <<std::endl <<"X["<<i<<","<<j<<"]= " << cplex.getValue(X[i][j])<<std::endl;
				}*/
			}
		}
		cplex.out() << endl;
		print_filtered_graph(g,temp);


	}
	catch (IloException& e) {
		cerr << "Concert exception caught: " << e << endl;
	}
	catch (...) {
		cerr << "Unknown exception caught" << endl;
	}
	//memory cleaning
	env.end();
}


int main(int argc, const char *argv[])
{
	typedef adjacency_list<vecS, vecS, undirectedS, no_property, property<edge_color_t, int>> Graph;
	typedef std::pair<int, int> Edge;
	typedef boost::graph_traits<Graph>::vertex_descriptor vertex_t;
	Graph::edge_iterator it, end;
	Graph g;
	int n_vertices, n_colors;
	//command-line processor

	try {
		std::ifstream ifn;
		po::options_description desc{ "Options" };
		desc.add_options()("help,h", "produce help message")
			("input-file,i", po::value< string >(), "input file")
			("include-path,I", po::value< string >(), "include path")
			("setup-file", po::value< string >(), "setup file");
		po::positional_options_description p;
		p.add("input-file", -1);


		po::variables_map vm;
		po::store(po::command_line_parser(argc, argv).
			options(desc).positional(p).run(), vm);
		po::notify(vm);

		if (vm.count("help")) {
			cout << desc << "\n";
			return 1;
		}
		else if (vm.count("input-file"))
		{
			std::cout << "Input files are: " << vm["input-file"].as<string>() << "\n";
			if (vm.count("include-path"))ifn.open((vm["include-path"].as<string>() + vm["input-file"].as<string>()).c_str(), ifstream::in);
			else ifn.open(vm["input-file"].as<string>().c_str(), ifstream::in);
			if (!ifn.is_open()) {
				std::cout << "error opening file" << std::endl;
				exit(EXIT_FAILURE);
			}
			dynamic_properties dp;
			dp.property("color", get(edge_color, g));
			read_graphml(ifn, g, dp);

			vector<string> vecI;
			split(vecI, vm["input-file"].as<string>(), is_any_of("-."), token_compress_off);
			if (vecI.size() == 6) {
				std::cout << vecI[0] << std::endl;
				n_vertices = stoi(vecI[0]);
				std::cout << vecI[2] << std::endl;
				n_colors = stoi(vecI[2]);
				std::cout << vecI[3] << std::endl;
				int k = stoi(vecI[3]);
				//add edges to super source vertex. remember!!!
				//vertex_t u = add_vertex(g);
				//n_vertices++;
				//for (int i = 0; i < n_vertices - 1; ++i) boost::add_edge(u, i, property<edge_color_t, int>(n_colors++), g);
				//std::tie(it, end) = boost::edges(g);
				//print_edges(it, end, g);
				solveModel(n_vertices, n_colors, k, g);
			}
			else {
				std::cout << "file wrong name format." << std::endl;
			}

		}
		else if (vm.count("setup-file")) {
			std::cout << "Not implemented yet" << std::endl;
		}
		else {
			std::cout << "see options(-h)." << std::endl;
		}


	}
	catch (const po::error &ex) {
		std::cout << ex.what();
		exit(EXIT_FAILURE);
	}
	catch (boost::exception &ex) {
		std::cout << boost::diagnostic_information(ex) << std::endl;
	}
	catch (std::exception &ex) {
		std::cout << ex.what();
		exit(EXIT_FAILURE);
	}

	return 0;
}