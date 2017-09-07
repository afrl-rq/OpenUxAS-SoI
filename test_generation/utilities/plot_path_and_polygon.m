function plot_path_and_polygon(pt_arr, poly_V)
figure
hold on;
plot(pt_arr(end,2), pt_arr(end, 1), 'x', 'color', 'r');
hold on;
plot(pt_arr(1, 2), pt_arr(1, 1), 'o', 'color', 'r');
hold on;
for i = 1:size(pt_arr, 1)
    plot(pt_arr(i, 2), pt_arr(i, 1), '.', 'color', 'b');
    hold on;
end
plot(pt_arr(:,2), pt_arr(:,1), 'color', 'b');
hold on;
P = Polyhedron(poly_V);
P.plot('wire', true, 'linewidth', 2, 'linecolor', 'r')
axis equal;
end