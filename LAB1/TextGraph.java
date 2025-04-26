import java.io.*;
import java.util.*;
import java.util.stream.*;
import java.nio.file.Files;
import java.nio.file.Paths;

/**
 * 从文本文件构建有向图，实现桥接词查询、新文本生成、最短路径计算、PageRank和随机游走
 */
public class TextGraph{ //public类
    
    //有向图
    static class Graph {
        private Map<String, Node> nodes;    //有向图节点集合
        private boolean directed;           //是否为有向图标记      /***此标记？****/
        
        //构建有向图方法
        public Graph(boolean directed) {    
            this.directed = directed;
            this.nodes = new HashMap<>();
        }
        
        //添加节点
        public void addNode(String name) {
            nodes.putIfAbsent(name.toLowerCase(), new Node(name.toLowerCase()));
        }
        
        //添加边
        public void addEdge(String source, String destination, int weight) {
            String src = source.toLowerCase();
            String dest = destination.toLowerCase();
            
            addNode(src);   //先添加两个结点
            addNode(dest);
            
            Node srcNode = nodes.get(src);
            Node destNode = nodes.get(dest);
            
            //更新边权重
            srcNode.addEdge(destNode, weight);  //添加边和权重
            if (!directed) {    //如果非有向图则添加对称边
                destNode.addEdge(srcNode, weight);
            }
        }
        
        //获取节点
        public Node getNode(String name) {
            return nodes.get(name.toLowerCase());
        }
        
        //检查是否包含节点
        public boolean containsNode(String name) {
            return nodes.containsKey(name.toLowerCase());
        }
        
        //获取所有节点
        public Collection<Node> getAllNodes() {
            return nodes.values();
        }
        
        //获取桥接词
        public List<String> getBridgeWords(String word1, String word2) {
            word1 = word1.toLowerCase();
            word2 = word2.toLowerCase();
            
            if (!containsNode(word1) || !containsNode(word2)) {
                return null;
            }
            
            Node node1 = getNode(word1);
            Node node2 = getNode(word2);
            
            //获取word1的邻居和word2的前驱的交集
            Set<String> neighbors = node1.getNeighbors();
            Set<String> predecessors = new HashSet<>();
            for (Node node : getAllNodes()) {
                if (node.hasEdgeTo(node2)) {
                    predecessors.add(node.getName());
                }
            }
            
            neighbors.retainAll(predecessors);
            return new ArrayList<>(neighbors);
        }
        
        //计算最短路径
        public PathResult calcShortestPath(String source, String destination) {
            source = source.toLowerCase();
            destination = destination.toLowerCase();
            
            if (!containsNode(source) || !containsNode(destination)) {
                return null;
            }
            
            //Dijkstra算法实现
            PriorityQueue<Node> queue = new PriorityQueue<>(Comparator.comparingInt(n -> n.getDistance()));
            Node start = getNode(source);
            start.setDistance(0);
            queue.add(start);
            
            Map<String, String> previous = new HashMap<>();
            Set<String> visited = new HashSet<>();
            
            while (!queue.isEmpty()) {
                Node current = queue.poll();
                visited.add(current.getName());
                
                for (Edge edge : current.getEdges()) {
                    Node neighbor = edge.getDestination();
                    if (visited.contains(neighbor.getName())) continue;
                    
                    int newDist = current.getDistance() + edge.getWeight();
                    if (newDist < neighbor.getDistance()) {
                        neighbor.setDistance(newDist);
                        previous.put(neighbor.getName(), current.getName());
                        queue.add(neighbor);
                    }
                }
            }
            
            //构建路径
            List<String> path = new ArrayList<>();
            String current = destination;
            while (current != null && !current.equals(source)) {
                path.add(current);
                current = previous.get(current);
                if (current == null) {
                    return new PathResult(null, Integer.MAX_VALUE); // 不可达
                }
            }
            path.add(source);
            Collections.reverse(path);
            
            int distance = getNode(destination).getDistance();
            
            //重置所有节点的距离
            for (Node node : getAllNodes()) {
                node.setDistance(Integer.MAX_VALUE);
            }
            
            return new PathResult(path, distance);
        }
        
        //计算某一结点到其他所有结点的最短路径
        public Map<String, PathResult> calcShortestPathsFrom(String source) {
            source = source.toLowerCase();
            
            if (!containsNode(source)) {
                return null;
            }
            
            // Dijkstra算法实现
            PriorityQueue<Node> queue = new PriorityQueue<>(Comparator.comparingInt(n -> n.getDistance()));
            Node start = getNode(source);
            start.setDistance(0);
            queue.add(start);
            
            Map<String, String> previous = new HashMap<>();
            Set<String> visited = new HashSet<>();
            
            while (!queue.isEmpty()) {
                Node current = queue.poll();
                visited.add(current.getName());
                
                for (Edge edge : current.getEdges()) {
                    Node neighbor = edge.getDestination();
                    if (visited.contains(neighbor.getName())) continue;
                    
                    int newDist = current.getDistance() + edge.getWeight();
                    if (newDist < neighbor.getDistance()) {
                        neighbor.setDistance(newDist);
                        previous.put(neighbor.getName(), current.getName());
                        queue.add(neighbor);
                    }
                }
            }
            
            // 构建所有路径结果
            Map<String, PathResult> allPaths = new HashMap<>();
            for (String nodeName : nodes.keySet()) {
                if (nodeName.equals(source)) continue;
                
                List<String> path = new ArrayList<>();
                String current = nodeName;
                while (current != null && !current.equals(source)) {
                    path.add(current);
                    current = previous.get(current);
                }
                
                if (current != null) { // 可达
                    path.add(source);
                    Collections.reverse(path);
                    allPaths.put(nodeName, new PathResult(path, getNode(nodeName).getDistance()));
                } else { // 不可达
                    allPaths.put(nodeName, new PathResult(null, Integer.MAX_VALUE));
                }
            }
            
            // 重置所有节点的距离
            for (Node node : getAllNodes()) {
                node.setDistance(Integer.MAX_VALUE);
            }
            
            return allPaths;
        }
        

        //计算PageRank,输入参数为阻尼因子和迭代参数
        public Map<String, Double> calcPageRank(double dampingFactor, int iterations) {
            Map<String, Double> pageRank = new HashMap<>();
            double initialValue = 1.0 / nodes.size();
            
            //初始化
            for (String node : nodes.keySet()) {
                pageRank.put(node, initialValue);
            }
            
            //迭代计算
            for (int i = 0; i < iterations; i++) {
                Map<String, Double> newPageRank = new HashMap<>();
                double danglingSum = 0.0;
                
                //计算悬挂节点的贡献
                for (Node node : getAllNodes()) {
                    if (node.getEdges().isEmpty()) {
                        danglingSum += pageRank.get(node.getName());
                    }
                }
                
                for (Node node : getAllNodes()) {
                    double sum = 0.0;
                    
                    //计算来自其他节点的贡献
                    for (Node incoming : getAllNodes()) {
                        if (incoming.hasEdgeTo(node)) {
                            sum += pageRank.get(incoming.getName()) / incoming.getOutDegree();
                        }
                    }
                    
                    //添加悬挂节点的均匀分布贡献
                    sum += danglingSum / nodes.size();
                    
                    //应用阻尼因子
                    newPageRank.put(node.getName(), 
                        (1 - dampingFactor) / nodes.size() + dampingFactor * sum);
                }
                
                pageRank = newPageRank;
            }
            
            return pageRank;
        }

        //随机游走
        public List<String> randomWalk() {
            List<String> walk = new ArrayList<>();
            if (nodes.isEmpty()) return walk;
            
            Random random = new Random();
            List<Node> nodeList = new ArrayList<>(getAllNodes());
            Node current = nodeList.get(random.nextInt(nodeList.size()));
            walk.add(current.getName());
            
            Set<String> visitedEdges = new HashSet<>();
            
            while (true) {
                List<Edge> edges = current.getEdges();
                if (edges.isEmpty()) break;
                
                Edge nextEdge = edges.get(random.nextInt(edges.size()));
                String edgeKey = current.getName() + "->" + nextEdge.getDestination().getName();
                
                if (visitedEdges.contains(edgeKey)) {
                    break; // 遇到重复边，停止
                }
                
                visitedEdges.add(edgeKey);
                current = nextEdge.getDestination();
                walk.add(current.getName());
            }
            
            return walk;
        }

        //生成DOT文件
        public String generateDot() {
            StringBuilder dot = new StringBuilder();
            dot.append("digraph G {\n");
            dot.append("  rankdir=LR;\n");
            dot.append("  node [shape=circle];\n");
            
            // 添加所有节点
            for (Node node : getAllNodes()) {
                dot.append("  \"").append(node.getName()).append("\";\n");
            }
            
            // 添加所有边
            for (Node node : getAllNodes()) {
                for (Edge edge : node.getEdges()) {
                    dot.append("  \"")
                       .append(node.getName())
                       .append("\" -> \"")
                       .append(edge.getDestination().getName())
                       .append("\" [label=\"")
                       .append(edge.getWeight())
                       .append("\"];\n");
                }
            }
            
            dot.append("}\n");
            return dot.toString();
        }

        //文件导出为图片
        public void exportGraph(String format, String outputFile) {
            try {
                // 生成临时DOT文件
                String dotContent = generateDot();
                Files.write(Paths.get("temp.dot"), dotContent.getBytes());
                
                // 调用Graphviz生成图片
                ProcessBuilder pb = new ProcessBuilder(
                    "dot", "-T"+format, "temp.dot", "-o", outputFile);
                Process process = pb.start();
                int exitCode = process.waitFor();
                
                if (exitCode != 0) {
                    System.err.println("Graphviz执行失败，请确保已安装Graphviz");
                } else {
                    System.out.println("图形已保存为: " + outputFile);
                }
                
                // 删除临时文件
                Files.deleteIfExists(Paths.get("temp.dot"));
            } catch (IOException | InterruptedException e) {
                System.err.println("导出图形失败: " + e.getMessage());
            }
        }
    }
    
    //节点
    static class Node {
        private String name;    //结点对应的字符串名称
        private List<Edge> edges;   //结点指出的边
        private int distance;   //用于最短路径计算
        
        //构建结点
        public Node(String name) {
            this.name = name;
            this.edges = new ArrayList<>();
            this.distance = Integer.MAX_VALUE;
        }
        
        //获取结点对应的字符串名称
        public String getName() {
            return name;
        }
        
        public void addEdge(Node destination, int weight) {
            //检查是否已存在边
            for (Edge edge : edges) {
                if (edge.getDestination().equals(destination)) {
                    edge.setWeight(edge.getWeight() + weight); //如果存在则只是增加权重，不再添加新边
                    return;
                }
            }
            edges.add(new Edge(destination, weight));
        }
        
        public List<Edge> getEdges() {
            return edges;
        }
        
        public Set<String> getNeighbors() {
            return edges.stream()
                .map(e -> e.getDestination().getName())
                .collect(Collectors.toSet());
        }
        
        public boolean hasEdgeTo(Node node) {
            return edges.stream().anyMatch(e -> e.getDestination().equals(node));
        }
        
        public int getOutDegree() {
            return edges.size();
        }
        
        public int getDistance() {
            return distance;
        }
        
        public void setDistance(int distance) {
            this.distance = distance;
        }
    }
    
    //有向边
    static class Edge {
        private Node destination;   //有向边的终点
        private int weight;         //有向边对应的权重
        
        //构建有向边
        public Edge(Node destination, int weight) {
            this.destination = destination;
            this.weight = weight;
        }
        
        public Node getDestination() {
            return destination;
        }
        
        public int getWeight() {
            return weight;
        }
        
        public void setWeight(int weight) {
            this.weight = weight;
        }
    }
    
    //最短路径结果类
    static class PathResult {
        private List<String> path;
        private int distance;
        
        public PathResult(List<String> path, int distance) {
            this.path = path;
            this.distance = distance;
        }
        
        public List<String> getPath() {
            return path;
        }
        
        public int getDistance() {
            return distance;
        }
    }
    
    //主程序
    public static void main(String[] args) {
        Scanner scanner = new Scanner(System.in);
        Graph graph = null;
        
        while (true) {
            System.out.println("************************");
            System.out.println("文本图分析与处理程序");
            System.out.println("1. 从文件构建图");
            System.out.println("2. 显示图结构");
            System.out.println("3. 查询桥接词");
            System.out.println("4. 生成新文本");
            System.out.println("5. 计算最短路径");
            System.out.println("6. 计算PageRank");
            System.out.println("7. 随机游走");
            System.out.println("8. 导出图形");
            System.out.println("0. 退出");
            System.out.println("************************");
            System.out.print("\n请选择功能(0-8): ");
            int choice;
            try {
                choice = scanner.nextInt();
                scanner.nextLine(); // 消耗换行符
            } catch (InputMismatchException e) {
                System.out.println("请输入有效数字!");
                scanner.nextLine(); // 清除无效输入
                continue;
            }
            
            switch (choice) {
                case 0:
                    System.out.println("程序退出。");
                    scanner.close();
                    return;
                    
                case 1:
                    System.out.print("请输入文本文件路径: ");
                    String filePath = scanner.nextLine();
                    graph = buildGraphFromFile(filePath);
                    if (graph != null) {
                        System.out.println("图构建成功!");
                    } else {
                        System.out.println("图构建失败，请检查文件路径。");
                    }
                    break;
                    
                case 2:
                    if (graph == null) {
                        System.out.println("请先构建图!");
                    } else {
                        showDirectedGraph(graph);
                    }
                    break;
                    
                case 3:
                    if (graph == null) {
                        System.out.println("请先构建图!");
                        break;
                    }
                    System.out.print("请输入第一个单词: ");
                    String word1 = scanner.nextLine();
                    System.out.print("请输入第二个单词: ");
                    String word2 = scanner.nextLine();
                    String result = queryBridgeWords(graph, word1, word2);
                    System.out.println(result);
                    break;
                    
                case 4:
                    if (graph == null) {
                        System.out.println("请先构建图!");
                        break;
                    }
                    System.out.print("请输入新文本: ");
                    String inputText = scanner.nextLine();
                    String newText = generateNewText(graph, inputText);
                    System.out.println("生成的新文本: " + newText);
                    break;
                    
                case 5:
                    if (graph == null) {
                        System.out.println("请先构建图!");
                        break;
                    }
                    System.out.print("请输入起始单词: ");
                    String startWord = scanner.nextLine();

                    System.out.print("请输入目标单词(留空将计算到所有其他节点的最短路径): ");
                    String endWord = scanner.nextLine();
                        
                    if (endWord.isEmpty()) {
                        // 计算单个起点到所有其他节点的最短路径
                        Map<String, PathResult> allPaths = graph.calcShortestPathsFrom(startWord);
                        if (allPaths == null) {
                            System.out.println("起始单词不存在!");
                            break;
                        }
                        
                        System.out.println("从 '" + startWord + "' 到其他所有单词的最短路径:");
                        allPaths.entrySet().stream()
                            .sorted(Comparator.comparingInt(e -> e.getValue().getDistance()))
                            .forEach(entry -> {
                                PathResult pathResult = entry.getValue();
                                System.out.printf("到 %s: ", entry.getKey());
                                if (pathResult.getPath() == null) {
                                    System.out.println("不可达");
                                } else {
                                    System.out.printf("路径: %s, 距离: %d%n",
                                        String.join(" -> ", pathResult.getPath()),
                                        pathResult.getDistance());
                                }
                            });
                    }
                    else {
                        // 计算单个起点到单个终点的最短路径
                        PathResult pathResult = graph.calcShortestPath(startWord, endWord);
                        if (pathResult == null || pathResult.getPath() == null) {
                            System.out.println("单词不存在或路径不可达!");
                        } else {
                            System.out.println("最短路径: " + String.join(" -> ", pathResult.getPath()));
                            System.out.println("路径长度: " + pathResult.getDistance());
                        }
                    }
                    break;
                    
                case 6:
                    if (graph == null) {
                        System.out.println("请先构建图!");
                        break;
                    }
                    System.out.print("请输入要查询的单词(留空显示全部): ");
                    String word = scanner.nextLine();
                    //保持阻尼因子为0.85，修改迭代次数为50
                    Map<String, Double> pageRanks = graph.calcPageRank(0.85, 50);
                    if (word.isEmpty()) {
                        System.out.println("所有单词的PageRank值:");
                        pageRanks.entrySet().stream()
                            .sorted(Map.Entry.<String, Double>comparingByValue().reversed())
                            .forEach(e -> System.out.printf("%s: %.4f%n", e.getKey(), e.getValue()));
                    } else {
                        word = word.toLowerCase();
                        if (pageRanks.containsKey(word)) {
                            System.out.printf("%s的PageRank值: %.4f%n", word, pageRanks.get(word));
                        } else {
                            System.out.println("单词不存在于图中!");
                        }
                    }
                    break;
                    
                case 7:
                    if (graph == null) {
                        System.out.println("请先构建图!");
                        break;
                    }
                    List<String> walk = graph.randomWalk();
                    System.out.println("随机游走结果: " + String.join(" -> ", walk));
                    System.out.print("是否保存到文件?(y/n): ");
                    String save = scanner.nextLine();
                    if (save.equalsIgnoreCase("y")) {
                        System.out.print("请输入文件名: ");
                        String fileName = scanner.nextLine();
                        saveRandomWalk(walk, fileName);
                    }
                    break;
                case 8:
                    if (graph == null) {
                        System.out.println("请先构建图!");
                        break;
                    }
                    System.out.print("请输入输出文件名(不含扩展名): ");
                    String outputFile = scanner.nextLine();
                    System.out.print("请选择格式(1-png, 2-svg, 3-pdf): ");
                    int formatChoice = scanner.nextInt();
                    scanner.nextLine(); // 消耗换行符
                    
                    String format;
                    switch (formatChoice) {
                        case 1: format = "png"; break;
                        case 2: format = "svg"; break;
                        case 3: format = "pdf"; break;
                        default:
                            System.out.println("无效选择，默认使用png");
                            format = "png";
                    }
                    graph.exportGraph(format, outputFile + "." + format);
                    break;
                    
                default:
                    System.out.println("无效选择，请重新输入!");
            }
        }
    }
    
    //从文件构建图
    public static Graph buildGraphFromFile(String filePath) {
        try {
            String content = new String(Files.readAllBytes(Paths.get(filePath)));
            return buildGraph(content);
        } catch (IOException e) {
            System.err.println("读取文件错误: " + e.getMessage());
            return null;
        }
    }
    
    //从文本内容构建图
    public static Graph buildGraph(String text) {
        // 预处理文本：替换所有非字母字符为空格，并转为小写
        String processed = text.replaceAll("[^a-zA-Z\\s]", " ")
                             .replaceAll("\\s+", " ")
                             .toLowerCase();
        
        String[] words = processed.split("\\s+");
        if (words.length == 0) return null;
        
        Graph graph = new Graph(true);
        
        // 构建图的边
        for (int i = 0; i < words.length - 1; i++) {
            String current = words[i];
            String next = words[i+1];
            graph.addEdge(current, next, 1);
        }
        
        return graph;
    }
    
    //显示有向图
    public static void showDirectedGraph(Graph graph) {
        System.out.println("有向图结构:");
        for (Node node : graph.getAllNodes()) {
            System.out.print(node.getName() + " -> ");
            List<Edge> edges = node.getEdges();
            if (edges.isEmpty()) {
                System.out.println("无出边");
                continue;
            }
            
            List<String> edgeStrings = edges.stream()
                .map(e -> e.getDestination().getName() + "(" + e.getWeight() + ")") //括号中显示边的权重值
                .collect(Collectors.toList());
            System.out.println(String.join(", ", edgeStrings));
        }
    }
    
    //查询桥接词
    public static String queryBridgeWords(Graph graph, String word1, String word2) {
        word1 = word1.toLowerCase();
        word2 = word2.toLowerCase();
        
        if (!graph.containsNode(word1) || !graph.containsNode(word2)) {
            return "No " + (!graph.containsNode(word1) ? word1 : word2) + " in the graph!";
        }
        
        List<String> bridgeWords = graph.getBridgeWords(word1, word2);
        if (bridgeWords == null || bridgeWords.isEmpty()) {
            return "No bridge words from " + word1 + " to " + word2 + "!";
        }
        
        if (bridgeWords.size() == 1) {
            return "The bridge word from " + word1 + " to " + word2 + " is: " + bridgeWords.get(0);
        } else {
            String last = bridgeWords.remove(bridgeWords.size() - 1);
            return "The bridge words from " + word1 + " to " + word2 + " are: " + 
                   String.join(", ", bridgeWords) + " and " + last;
        }
    }
    
    //生成新文本
    public static String generateNewText(Graph graph, String inputText) {
        // 预处理输入文本
        String processed = inputText.replaceAll("[^a-zA-Z\\s]", " ")
                                   .replaceAll("\\s+", " ")
                                   .toLowerCase();
        
        String[] words = processed.split("\\s+");
        if (words.length == 0) return inputText;
        
        List<String> result = new ArrayList<>();
        result.add(words[0]);
        
        Random random = new Random();
        
        for (int i = 0; i < words.length - 1; i++) {
            String current = words[i];
            String next = words[i+1];
            
            // 查找桥接词
            List<String> bridgeWords = graph.getBridgeWords(current, next);
            if (bridgeWords != null && !bridgeWords.isEmpty()) {
                // 随机选择一个桥接词
                String bridge = bridgeWords.get(random.nextInt(bridgeWords.size()));
                result.add(bridge);
            }
            
            result.add(next);
        }
        
        // 保留原始文本的大小写和标点
        String[] originalWords = inputText.split("\\s+");
        if (originalWords.length == result.size()) {
            // 尝试保留原始大小写
            for (int i = 0; i < originalWords.length; i++) {
                String original = originalWords[i];
                if (original.length() > 0 && Character.isUpperCase(original.charAt(0))) {
                    String word = result.get(i);
                    if (word.length() > 0) {
                        result.set(i, Character.toUpperCase(word.charAt(0)) + word.substring(1));
                    }
                }
            }
        }
        
        return String.join(" ", result);
    }
    
    //保存随机游走结果到文件
    public static void saveRandomWalk(List<String> walk, String fileName) {
        try (PrintWriter writer = new PrintWriter(fileName)) {
            writer.println(String.join(" ", walk));
            System.out.println("随机游走结果已保存到 " + fileName);
        } catch (FileNotFoundException e) {
            System.err.println("无法创建文件: " + e.getMessage());
        }
    }
}